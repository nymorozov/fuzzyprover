//	В массиве А есть В	//
function inAexistsB (A,B) {
	var exist = false;
	B.forEach( function(item, i, arr) {
			if(A == item) exist = true;
	})
	return exist;
}
//	Вектор уникальных элементов	//
function retVectOfUniqElem(VECT) {	
	var retVect = [];
	nextInput:
	for(var i=0; i<VECT.length; i++) {
		var str = VECT[i];
		for(var j=0;j<retVect.length;j++) {
			if(retVect[j] == str) continue nextInput;
		}
		retVect.push(str);
	}
	return retVect;
}	

document.body.razdel = ",";

//	ПО-дерево	//
var FAL = "\\mathbb{F}";
var FALvect = [];
FALvect.push(FAL);
var TRU = "\\mathbb{T}";
var TRUvect = [];
TRUvect.push(TRU);
function treePO(q,A, PARENT) {
	this.isquest = q;
	this.proposit = A.concat();
	this.deti = [];
	this.otec = PARENT;
}
// Прототип	//
treePO.prototype = {
	newDet: function(Q,A){
		sibl = new treePO (Q,A, this);
		this.deti.push(sibl);
		delete sibl;
	},
	retNewDet: function(Q,A){
		sibl = new treePO (Q,A, this);
		this.deti.push(sibl);
		return sibl;
	},
	retNewBase: function(Q,A,W){
		sibl = new treePO (Q,A, this);
		sibl.propositWeights = W.concat()
		this.deti.push(sibl);
		return sibl;
	},
	retNewDetWithW: function(Q,A,W){
		sibl = new treePO (Q,A, this);
		sibl.weight = W;
		this.deti.push(sibl);
		return sibl;
	},
	delPOUzel: function() {
		var father = this.otec;
		father.deti.splice(father.deti.indexOf(this),1);
		this.deti.forEach(function(item, i, arr) {
			item.otec=father;
			father.deti.push(item);
		});
	},
	otrezPOUzel: function() {
		var parent = this.otec;
		this.otec = undefined;
		parent.deti.splice(parent.deti.indexOf(this),1);
		delete parent;
	},
	returnVectOfStr : function() {
		var razdel = document.body.razdel;
		var retStr = "";
		if(this.isquest == 1) {
			retStr += "-~\\forall";	
			retStr += "\\!:\\!";
		}
		if(this.isquest == 0) {
			 retStr += "-~\\exists";
			 if(this.weight != undefined) retStr+= ("_{("+this.weight+")}");
			 ////////////// LABEL /////////////
			 if(this.ref != undefined) retStr += "^{"+this.ref+"}";
			 //////////////////////////////////
			 retStr += "\\!:\\!";
		}
		var thisNode = this;
		this.proposit.forEach(function(item, i, arr) {
			retStr += item;
			if(thisNode.propositWeights != undefined) retStr += ("_{("+thisNode.propositWeights[i]+")}");
			if(i != arr.length-1) retStr+=razdel;
		});
		delete thisNode;
		delete razdel;
		return retStr;
	},
	stepShowPOTeX : function (div) {
		div.innerHTML += this.returnVectOfStr();
		if(this.deti.length == 0) {
			div.innerHTML += "\\\\";	
		}
		if(this.deti.length > 0) {
			if(this.deti.length > 1) { div.innerHTML += "\\begin{cases}";}
			this.deti.forEach(function (item, i, arr) {
				item.stepShowPOTeX(div); 
			});
			if(this.deti.length > 1) { div.innerHTML += "\\end{cases}\\\\";}
		}
	},
	addPOTeX : function(div,title){
		div.innerHTML += "\\begin{equation}";
		if(title != undefined) div.innerHTML+=title;
		
		this.stepShowPOTeX(div);
		
		div.innerHTML += "\\end{equation}";
		MathJax.Hub.Queue(["Typeset",MathJax.Hub]);
	},
	returnPOTeX : function(div,title){
			div.innerHTML = "";
			this.addPOTeX(div,title);
	},
	stepGetStrPOTeX : function () {
		var retStr = this.returnVectOfStr();
		if(this.deti.length == 0) {
			retStr += "\\\\";	
		}
		if(this.deti.length > 0) {
			if(this.deti.length > 1) { retStr += "\\begin{cases}";}
			this.deti.forEach(function (item, i, arr) {
				retStr += item.stepGetStrPOTeX(); 
			});
			if(this.deti.length > 1) { retStr += "\\end{cases}\\\\";}
		}
		return retStr;
	},
	getStrPOTeX : function(title){
		var retStr = "\\begin{equation}";
		if(title != undefined) retStr+=title;
		
		retStr += this.stepGetStrPOTeX();
		
		retStr += "\\end{equation}";
		return retStr;
	},
	negate : function() {
		this.isquest = (this.isquest+1)%2;
		this.deti.forEach(function(item, i, arr) { // Минимум
			item.negate();
		});
		if(this.deti.length == 0){this.newDet(0,FALvect);}
	},
	addBranch : function(branchRoot) {
		if(branchRoot.isquest != this.isquest){
			this.deti.push(branchRoot);
			branchRoot.otec = this;
		} else {
			var kvantorSwitch = (this.isquest+1)%2;
			var sibl = this.retNewDet(kvantorSwitch,TRUvect);
			if(branchRoot.ref != undefined) sibl.ref = branchRoot.ref;
			sibl.deti.push(branchRoot);
			branchRoot.otec = sibl;
			delete sibl,kvantorSwitch;
		}
	},
	copyPOOne : function(PARENT) {
		var Sibl = PARENT.retNewDet(this.isquest,this.proposit);
		if(this.ref != undefined) Sibl.ref = this.ref;
		if(this.weight != undefined) Sibl.weight = this.weight;
		this.deti.forEach(function(item, i, arr) {
			item.copyPOOne(Sibl);
		});
	},
	copyPO : function() {
		var newroot = new treePO (this.isquest,this.proposit, undefined);
		if(this.propositWeights != undefined) newroot.propositWeights = this.propositWeights.concat();
		this.copyPOOne(newroot);
		newroot.deti[0].delPOUzel();
		return newroot;
	}
}

///////////////////////	Применение правила w	///////////////////////
//	Вопрос в базе	//
treePO.prototype.isQuestInBase = function(questNode){
	var retFlag = 1;
	var base = this;
	questNode.proposit.forEach(function(item, i, arr) {
		if(!inAexistsB(item,base.proposit)) retFlag = 0;
	});
	return retFlag;
}

//	Устранение тривиального вопроса	//
treePO.prototype.eraseTriv = function() {
	
	var parent = this.otec;
	
	if(this.deti.length == 1){
		var sibl = this.deti[0];
		parent.proposit = parent.proposit.concat(sibl.proposit);
		parent.proposit = retVectOfUniqElem(parent.proposit);
		var weigthBuf = 1;
		this.proposit.forEach(function(item, i, arr) {
			weigthBuf = Math.min(parent.propositWeights[parent.proposit.indexOf(item)],weigthBuf) ;
		});
		
		weigthBuf *= sibl.weight;
		sibl.proposit.forEach(function(item, i, arr) {
			parent.propositWeights.push(weigthBuf);
		});
		delete weigthBuf;
		////////////// проверяем базу //////////
		parent.baseAudit();
		
		////////////// показать ссылку ///////////
		if(this.ref != undefined){
			/*
proofLive.innerHTML += "&"+document.body.proofHistory.length+")~"+parent.ref+" - "+mapLinks[this.ref]+" : "+this.returnVectOfStr()+"~\\to~"+sibl.returnVectOfStr()+"\\\\";
			proofLive.innerHTML += "\\end{aligned}\\begin{aligned}";
*/
			
			/*
var bufProofStep = new proofStep(document.body.proofHistory.length,parent.ref,mapLinks[this.ref],this.returnVectOfStr(),sibl.returnVectOfStr());
			proofConseq.push(bufProofStep);
			delete bufProofStep;
*/
		}
		
		sibl.delPOUzel();
		this.delPOUzel();
		delete sibl;
	} else {
	if(this.deti.length > 1){
		this.otrezPOUzel();
		var ded = parent.otec;
		var thisNode = this;
		this.deti.forEach(function(item, i, arr) {
			if(i < arr.length-1) {
				var baseCopy = parent.copyPO();
				baseNumber = baseNumber+"I";
				baseCopy.ref = baseNumber;
				// proofLive.innerHTML += "&"+document.body.proofHistory.length+")~"+parent.ref+"~\\to~"+baseCopy.ref+"\\\\";
				
				/*
var bufProofStep = new proofStep(document.body.proofHistory.length,parent.ref,undefined,parent.ref,baseCopy.ref);
			proofConseq.push(bufProofStep);
			delete bufProofStep;
*/
				baseCopy.retNewDetWithW(1,thisNode.proposit,thisNode.weight).addBranch(item);
				item.otec.eraseTriv();
				ded.addBranch(baseCopy);
				delete baseCopy;
			} else {
				parent.retNewDetWithW(1,thisNode.proposit,thisNode.weight).addBranch(item);
				item.otec.eraseTriv();	
			}	
		});
		delete ded;
	}}
	delete parent;
}
//	Само доказательство	//
document.body.proofHistory = [];
treePO.prototype.proveBase = function()	{
	var base = this;
	var smthHappendFlag = true;
	while(smthHappendFlag && !inAexistsB(FAL,base.proposit)) {
		smthHappendFlag = false;
		this.deti.forEach(function(item, i, arr) {
			if(base.isQuestInBase(item) && !inAexistsB(FAL,base.proposit)) {
				item.eraseTriv();
				if(document.body.proofHistory.length > 1){
					document.body.proofHistory.push( base.otec.getStrPOTeX("\\omega^{"+document.body.proofHistory.length+"}F=") );
				} else {
					document.body.proofHistory.push( base.otec.getStrPOTeX("\\omega F=") );
				}
				
				smthHappendFlag = true;
			}
		});
	}
	delete base,smthHappendFlag;
	if(inAexistsB(FAL,this.proposit)) {
		return true;
	} else {
		return false;
	}
}
treePO.prototype.prove = function()	{
	document.body.proofHistory.push( this.getStrPOTeX("F=") );
	var i = 0;
	while(i<this.deti.length) {
		var result = this.deti[i].proveBase();
		if(result == false){
			return false;
		}
		i++;
	}
	var retRes = true;
	this.deti.forEach(function(item, i, arr) {
		if(!inAexistsB(FAL,item.proposit)) retRes=false;
	});
	if(retRes) {return true;}
}
//	Добавляем ссылку на уравнение	//
var linkCounter = 0;
treePO.prototype.addLink = function(LINK) {
	if(this.isquest == 0 && this.propositWeights == undefined) {
		this.ref = LINK+"_{"+linkCounter+"}";
		linkCounter++;
	}
	this.deti.forEach(function(item, i, arr) {
		item.addLink(LINK);
	});
}
//	Проверяем базу	//
treePO.prototype.baseAudit = function() {
	var flag = true;
	while(flag) {
		flag = false;
		for(var i=0;i<this.propositWeights.length;i++) {
			if(this.propositWeights[i] == 0) {
				this.proposit.splice(i, 1);
				this.propositWeights.splice(i, 1);
				i--;
				flag = true;
			}
		}
		
		thisNode = this;
		this.proposit.forEach(function(item, i, arr) {
			if(inAexistsB ("{\\neg}"+item,arr)) {
				var negIndex = arr.indexOf("{\\neg}"+item);
				thisNode.propositWeights[i] = Math.min(thisNode.propositWeights[i],1-thisNode.propositWeights[negIndex]);
				thisNode.proposit.splice(negIndex, 1);
				thisNode.propositWeights.splice(negIndex, 1);
				delete negIndex;
				flag = true;
			}
		});
	}

}
// Действие //
function action(NAME,W) {
	this.name = NAME;
	this.w = W;
}
action.prototype.show = function() {
	alert(this.name+" ("+this.w+")");
}
//	Выводим вектор действий	//
treePO.prototype.retActions = function() {
	var bufActions = [];
	var thisNode = this;
	this.proposit.forEach(function(item, i, arr) {
		if(item.indexOf("{\\bf") == 0) {
			var bufElem = new action(item,thisNode.propositWeights[i]);
			bufActions.push(bufElem);
			delete bufElem;
		}
	});
	delete thisNode;
	return bufActions;
}