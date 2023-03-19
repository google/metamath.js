include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "cmee.mm"
include "co.mm"
include "cdib.mm"
include "cdvh.mm"
include "clsm.mm"
include "cbs.mm"
include "cjn.mm"
include "wceq.mm"
include "simpl.mm"
include "eqid.mm"
include "atbase.mm"
include "ad2antrl.mm"
include "simprr.mm"
include "simpr.mm"
include "cp0.mm"
include "lhpmat.mm"
include "oveq2d.mm"
include "col.mm"
include "hlol.mm"
include "ad2antrr.mm"
include "olj01.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "dihvalcq.mm"
include "syl122anc.mm"
include "c0g.mm"
include "csn.mm"
include "fveq2d.mm"
include "dib0.mm"
include "adantr.mm"
include "csubg.mm"
include "clmod.mm"
include "clss.mm"
include "dvhlmod.mm"
include "diclss.mm"
include "lsssubg.mm"
include "lsm01.mm"
include "syl.mm"

theorem dihvalcqat
  let cA: class A
  let cQ: class Q
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let c.le: class .<_
  let cW: class W
  assume dihvalcqat.l: |- .<_ = ( le ` K )
  assume dihvalcqat.a: |- A = ( Atoms ` K )
  assume dihvalcqat.h: |- H = ( LHyp ` K )
  assume dihvalcqat.j: |- J = ( ( DIsoC ` K ) ` W )
  assume dihvalcqat.i: |- I = ( ( DIsoH ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( Q e. A /\ -. Q .<_ W ) ) -> ( I ` Q ) = ( J ` Q ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cQ
    cA
    wcel
    #
    cQ
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    wa
    #
    cQ
    cI
    cfv
    #
    cQ
    cJ
    cfv
    #
    cQ
    cW
    cK
    cmee
    cfv
    #
    co
    #
    cW
    cK
    cdib
    cfv
    cfv
    #
    cfv
    #
    cW
    cK
    cdvh
    cfv
    cfv
    #
    clsm
    cfv
    #
    co
    #
    @8
    @6
    @2
    cQ
    cK
    cbs
    cfv
    #
    wcel
    #
    @4
    @5
    cQ
    @10
    cK
    cjn
    cfv
    #
    co
    #
    cQ
    wceq
    @7
    @15
    wceq
    @2
    @5
    simpl
    #
    @3
    @17
    @2
    @4
    cA
    @16
    cQ
    cK
    @16
    eqid
    #
    dihvalcqat.a
    atbase
    ad2antrl
    #
    @2
    @3
    @4
    simprr
    @2
    @5
    simpr
    @6
    @19
    cQ
    cK
    cp0
    cfv
    #
    @18
    co
    #
    cQ
    @6
    @10
    @23
    cQ
    @18
    cA
    cQ
    cH
    cK
    c.le
    @9
    cW
    @23
    dihvalcqat.l
    @9
    eqid
    #
    @23
    eqid
    #
    dihvalcqat.a
    dihvalcqat.h
    lhpmat
    #
    oveq2d
    @6
    cK
    col
    wcel
    #
    @17
    @24
    cQ
    wceq
    @0
    @28
    @1
    @5
    cK
    hlol
    ad2antrr
    @22
    @16
    @18
    cK
    cQ
    @23
    @21
    @18
    eqid
    #
    @26
    olj01
    syl2anc
    eqtrd
    cA
    @16
    cJ
    @11
    @14
    cQ
    @13
    cH
    cI
    @18
    cK
    c.le
    @9
    cW
    cQ
    @21
    dihvalcqat.l
    @29
    @25
    dihvalcqat.a
    dihvalcqat.h
    dihvalcqat.i
    @11
    eqid
    #
    dihvalcqat.j
    @13
    eqid
    #
    @14
    eqid
    #
    dihvalcq
    syl122anc
    @6
    @15
    @8
    @13
    c0g
    cfv
    #
    csn
    #
    @14
    co
    #
    @8
    @6
    @12
    @34
    @8
    @14
    @6
    @12
    @23
    @11
    cfv
    #
    @34
    @6
    @10
    @23
    @11
    @27
    fveq2d
    @2
    @36
    @34
    wceq
    @5
    @13
    cH
    @11
    cK
    @33
    cW
    @23
    @26
    dihvalcqat.h
    @30
    @31
    @33
    eqid
    #
    dib0
    adantr
    eqtrd
    oveq2d
    @6
    @8
    @13
    csubg
    cfv
    wcel
    #
    @35
    @8
    wceq
    @6
    @13
    clmod
    wcel
    @8
    @13
    clss
    cfv
    #
    wcel
    @38
    @6
    @13
    cH
    cK
    cW
    dihvalcqat.h
    @31
    @20
    dvhlmod
    cA
    cQ
    @39
    @13
    cH
    cJ
    cK
    c.le
    cW
    dihvalcqat.l
    dihvalcqat.a
    dihvalcqat.h
    @31
    dihvalcqat.j
    @39
    eqid
    #
    diclss
    @39
    @8
    @13
    @40
    lsssubg
    syl2anc
    @14
    @13
    @8
    @33
    @37
    @32
    lsm01
    syl
    eqtrd
    eqtrd
end
