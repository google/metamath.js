include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "ctendo.mm"
include "cfv.mm"
include "cplusg.mm"
include "cvsca.mm"
include "csca.mm"
include "cltrn.mm"
include "cxp.mm"
include "eqidd.mm"
include "cbs.mm"
include "wceq.mm"
include "eqid.mm"
include "dvhbase.mm"
include "eqcomd.mm"
include "adantr.mm"
include "dvhvbase.mm"
include "clss.mm"
include "a1i.mm"
include "dicssdvh.mm"
include "sseqtr4d.mm"
include "dicn0.mm"
include "cv.mm"
include "w3a.mm"
include "co.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr1.mm"
include "simpr2.mm"
include "dicvscacl.mm"
include "syl112anc.mm"
include "simpr3.mm"
include "dicvaddcl.mm"
include "islssd.mm"

theorem diclss
  let cA: class A
  let cQ: class Q
  let cS: class S
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  assume diclss.l: |- .<_ = ( le ` K )
  assume diclss.a: |- A = ( Atoms ` K )
  assume diclss.h: |- H = ( LHyp ` K )
  assume diclss.u: |- U = ( ( DVecH ` K ) ` W )
  assume diclss.i: |- I = ( ( DIsoC ` K ) ` W )
  assume diclss.s: |- S = ( LSubSp ` U )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( Q e. A /\ -. Q .<_ W ) ) -> ( I ` Q ) e. S )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    #
    wa
    #
    vx
    cW
    cK
    ctendo
    cfv
    cfv
    #
    cU
    cplusg
    cfv
    #
    cS
    cU
    cvsca
    cfv
    #
    cQ
    cI
    cfv
    #
    cU
    csca
    cfv
    #
    cW
    cK
    cltrn
    cfv
    cfv
    #
    @3
    cxp
    #
    cU
    va
    vb
    @2
    @7
    eqidd
    @0
    @3
    @7
    cbs
    cfv
    #
    wceq
    @1
    @0
    @10
    @3
    @10
    cU
    @3
    @7
    cH
    cK
    cW
    chlt
    diclss.h
    @3
    eqid
    #
    diclss.u
    @7
    eqid
    @10
    eqid
    dvhbase
    eqcomd
    adantr
    @0
    @9
    cU
    cbs
    cfv
    #
    wceq
    @1
    @0
    @12
    @9
    @8
    cU
    @3
    cH
    cK
    @12
    cW
    chlt
    diclss.h
    @8
    eqid
    @11
    diclss.u
    @12
    eqid
    #
    dvhvbase
    eqcomd
    adantr
    #
    @2
    @4
    eqidd
    @2
    @5
    eqidd
    cS
    cU
    clss
    cfv
    wceq
    @2
    diclss.s
    a1i
    @2
    @6
    @12
    @9
    cA
    cQ
    cU
    cH
    cI
    cK
    c.le
    @12
    cW
    diclss.l
    diclss.a
    diclss.h
    diclss.i
    diclss.u
    @13
    dicssdvh
    @14
    sseqtr4d
    cA
    cQ
    cH
    cI
    cK
    c.le
    cW
    diclss.l
    diclss.a
    diclss.h
    diclss.i
    dicn0
    @2
    vx
    cv
    #
    @3
    wcel
    #
    va
    cv
    #
    @6
    wcel
    #
    vb
    cv
    #
    @6
    wcel
    #
    w3a
    #
    wa
    #
    @0
    @1
    @15
    @17
    @5
    co
    #
    @6
    wcel
    #
    @20
    @23
    @19
    @4
    co
    @6
    wcel
    @0
    @1
    @21
    simpll
    #
    @0
    @1
    @21
    simplr
    #
    @22
    @0
    @1
    @16
    @18
    @24
    @25
    @26
    @2
    @16
    @18
    @20
    simpr1
    @2
    @16
    @18
    @20
    simpr2
    cA
    cQ
    @5
    cU
    @3
    cH
    cI
    cK
    c.le
    cW
    @15
    @17
    diclss.l
    diclss.a
    diclss.h
    @11
    diclss.u
    diclss.i
    @5
    eqid
    dicvscacl
    syl112anc
    @2
    @16
    @18
    @20
    simpr3
    cA
    @4
    cQ
    cU
    cH
    cI
    cK
    c.le
    cW
    @23
    @19
    diclss.l
    diclss.a
    diclss.h
    diclss.u
    diclss.i
    @4
    eqid
    dicvaddcl
    syl112anc
    islssd
end
