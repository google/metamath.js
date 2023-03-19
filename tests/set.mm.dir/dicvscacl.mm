include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "w3a.mm"
include "co.mm"
include "c1st.mm"
include "cid.mm"
include "c2nd.mm"
include "ccom.mm"
include "cop.mm"
include "cltrn.mm"
include "cxp.mm"
include "wceq.mm"
include "simp1.mm"
include "simp3l.mm"
include "wss.mm"
include "cbs.mm"
include "eqid.mm"
include "dicssdvh.mm"
include "dvhvbase.mm"
include "eqcomd.mm"
include "adantr.mm"
include "sseqtr4d.mm"
include "3adant3.mm"
include "simp3r.mm"
include "sseldd.mm"
include "dvhvsca.mm"
include "syl12anc.mm"
include "fvi.mm"
include "syl.mm"
include "coeq1d.mm"
include "opeq2d.mm"
include "eqtr4d.mm"
include "coc.mm"
include "cv.mm"
include "crio.mm"
include "dicelval1sta.mm"
include "3adant3l.mm"
include "fveq2d.mm"
include "wf.mm"
include "dicelval2nd.mm"
include "tendof.mm"
include "syl2anc.mm"
include "lhpocnel.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "ltrniotacl.mm"
include "syl3anc.mm"
include "fvco3.mm"
include "fveq1d.mm"
include "tendococl.mm"
include "eqeltrd.mm"
include "wb.mm"
include "fvex.mm"
include "coex.mm"
include "dicopelval.mm"
include "mpbir2and.mm"

theorem dicvscacl
  let cA: class A
  let cQ: class Q
  let c.x: class .x.
  let cU: class U
  let cE: class E
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let cX: class X
  let cY: class Y
  let vg: setvar g
  assume dicvscacl.l: |- .<_ = ( le ` K )
  assume dicvscacl.a: |- A = ( Atoms ` K )
  assume dicvscacl.h: |- H = ( LHyp ` K )
  assume dicvscacl.e: |- E = ( ( TEndo ` K ) ` W )
  assume dicvscacl.u: |- U = ( ( DVecH ` K ) ` W )
  assume dicvscacl.i: |- I = ( ( DIsoC ` K ) ` W )
  assume dicvscacl.s: |- .x. = ( .s ` U )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( X e. E /\ Y e. ( I ` Q ) ) ) -> ( X .x. Y ) e. ( I ` Q ) )

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
    cX
    cE
    wcel
    #
    cY
    cQ
    cI
    cfv
    #
    wcel
    #
    wa
    #
    w3a
    #
    cX
    cY
    c.x
    co
    #
    cY
    c1st
    cfv
    #
    cX
    cfv
    #
    cX
    cid
    cfv
    #
    cY
    c2nd
    cfv
    #
    ccom
    #
    cop
    #
    @3
    @6
    @7
    @9
    cX
    @11
    ccom
    #
    cop
    #
    @13
    @6
    @0
    @2
    cY
    cW
    cK
    cltrn
    cfv
    cfv
    #
    cE
    cxp
    #
    wcel
    @7
    @15
    wceq
    @0
    @1
    @5
    simp1
    #
    @0
    @1
    @2
    @4
    simp3l
    #
    @6
    @3
    @17
    cY
    @0
    @1
    @3
    @17
    wss
    @5
    @0
    @1
    wa
    @3
    cU
    cbs
    cfv
    #
    @17
    cA
    cQ
    cU
    cH
    cI
    cK
    c.le
    @20
    cW
    dicvscacl.l
    dicvscacl.a
    dicvscacl.h
    dicvscacl.i
    dicvscacl.u
    @20
    eqid
    #
    dicssdvh
    @0
    @17
    @20
    wceq
    @1
    @0
    @20
    @17
    @16
    cU
    cE
    cH
    cK
    @20
    cW
    chlt
    dicvscacl.h
    @16
    eqid
    #
    dicvscacl.e
    dicvscacl.u
    @21
    dvhvbase
    eqcomd
    adantr
    sseqtr4d
    3adant3
    @0
    @1
    @2
    @4
    simp3r
    sseldd
    cX
    @16
    c.x
    cU
    cE
    cY
    cH
    cK
    chlt
    cW
    dicvscacl.h
    @22
    dicvscacl.e
    dicvscacl.u
    dicvscacl.s
    dvhvsca
    syl12anc
    @6
    @12
    @14
    @9
    @6
    @10
    cX
    @11
    @6
    @2
    @10
    cX
    wceq
    @19
    cX
    cE
    fvi
    syl
    coeq1d
    #
    opeq2d
    eqtr4d
    @6
    @13
    @3
    wcel
    #
    @9
    cW
    cK
    coc
    cfv
    #
    cfv
    #
    vg
    cv
    cfv
    cQ
    wceq
    vg
    @16
    crio
    #
    @12
    cfv
    #
    wceq
    #
    @12
    cE
    wcel
    #
    @6
    @9
    @27
    @14
    cfv
    #
    @28
    @6
    @9
    @27
    @11
    cfv
    #
    cX
    cfv
    #
    @31
    @6
    @8
    @32
    cX
    @0
    @1
    @4
    @8
    @32
    wceq
    @2
    cA
    @26
    cQ
    @16
    vg
    cH
    cI
    cK
    c.le
    chlt
    cW
    cY
    dicvscacl.l
    dicvscacl.a
    dicvscacl.h
    @26
    eqid
    #
    @22
    dicvscacl.i
    dicelval1sta
    3adant3l
    fveq2d
    @6
    @16
    @16
    @11
    wf
    #
    @27
    @16
    wcel
    #
    @31
    @33
    wceq
    @6
    @0
    @11
    cE
    wcel
    #
    @35
    @18
    @0
    @1
    @4
    @37
    @2
    cA
    cQ
    cE
    cH
    cI
    cK
    c.le
    cW
    cY
    dicvscacl.l
    dicvscacl.a
    dicvscacl.h
    dicvscacl.e
    dicvscacl.i
    dicelval2nd
    3adant3l
    #
    @11
    @16
    cE
    cH
    cK
    chlt
    cW
    dicvscacl.h
    @22
    dicvscacl.e
    tendof
    syl2anc
    @6
    @0
    @26
    cA
    wcel
    @26
    cW
    c.le
    wbr
    wn
    wa
    #
    @1
    @36
    @18
    @0
    @1
    @39
    @5
    cA
    cH
    cK
    c.le
    @25
    cW
    dicvscacl.l
    @25
    eqid
    dicvscacl.a
    dicvscacl.h
    lhpocnel
    3ad2ant1
    @0
    @1
    @5
    simp2
    cA
    @26
    cQ
    @16
    vg
    @27
    cH
    cK
    c.le
    cW
    dicvscacl.l
    dicvscacl.a
    dicvscacl.h
    @22
    @27
    eqid
    ltrniotacl
    syl3anc
    @16
    @16
    @27
    cX
    @11
    fvco3
    syl2anc
    eqtr4d
    @6
    @27
    @12
    @14
    @23
    fveq1d
    eqtr4d
    @6
    @12
    @14
    cE
    @23
    @6
    @0
    @2
    @37
    @14
    cE
    wcel
    @18
    @19
    @38
    cX
    @11
    cE
    cH
    cK
    cW
    dicvscacl.h
    dicvscacl.e
    tendococl
    syl3anc
    eqeltrd
    @0
    @1
    @24
    @29
    @30
    wa
    wb
    @5
    cA
    @26
    cQ
    @12
    @16
    vg
    cE
    @9
    cH
    cI
    cK
    c.le
    chlt
    cW
    dicvscacl.l
    dicvscacl.a
    dicvscacl.h
    @34
    @22
    dicvscacl.e
    dicvscacl.i
    @8
    cX
    fvex
    @10
    @11
    cX
    cid
    fvex
    cY
    c2nd
    fvex
    coex
    dicopelval
    3adant3
    mpbir2and
    eqeltrd
end
