include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "w3a.mm"
include "co.mm"
include "c1st.mm"
include "ccom.mm"
include "c2nd.mm"
include "csca.mm"
include "cplusg.mm"
include "cop.mm"
include "cltrn.mm"
include "ctendo.mm"
include "cxp.mm"
include "wceq.mm"
include "simp1.mm"
include "wss.mm"
include "cbs.mm"
include "eqid.mm"
include "dicssdvh.mm"
include "dvhvbase.mm"
include "eqcomd.mm"
include "adantr.mm"
include "sseqtr4d.mm"
include "3adant3.mm"
include "simp3l.mm"
include "sseldd.mm"
include "simp3r.mm"
include "dvhvadd.mm"
include "syl12anc.mm"
include "coc.mm"
include "cv.mm"
include "crio.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "dicelval2nd.mm"
include "3adant3r.mm"
include "3adant3l.mm"
include "lhpocnel.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "ltrniotacl.mm"
include "syl3anc.mm"
include "tendospdi2.mm"
include "dvhfplusr.mm"
include "oveqd.mm"
include "fveq1d.mm"
include "dicelval1sta.mm"
include "coeq12d.mm"
include "3eqtr4rd.mm"
include "tendoplcl.mm"
include "eqeltrd.mm"
include "wb.mm"
include "fvex.mm"
include "coex.mm"
include "ovex.mm"
include "dicopelval.mm"
include "mpbir2and.mm"

theorem dicvaddcl
  let cA: class A
  let c.pl: class .+
  let cQ: class Q
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let cX: class X
  let cY: class Y
  let vg: setvar g
  let vh: setvar h
  let vs: setvar s
  let vt: setvar t
  assume dicvaddcl.l: |- .<_ = ( le ` K )
  assume dicvaddcl.a: |- A = ( Atoms ` K )
  assume dicvaddcl.h: |- H = ( LHyp ` K )
  assume dicvaddcl.u: |- U = ( ( DVecH ` K ) ` W )
  assume dicvaddcl.i: |- I = ( ( DIsoC ` K ) ` W )
  assume dicvaddcl.p: |- .+ = ( +g ` U )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( X e. ( I ` Q ) /\ Y e. ( I ` Q ) ) ) -> ( X .+ Y ) e. ( I ` Q ) )

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
    cQ
    cI
    cfv
    #
    wcel
    #
    cY
    @2
    wcel
    #
    wa
    #
    w3a
    #
    cX
    cY
    c.pl
    co
    #
    cX
    c1st
    cfv
    #
    cY
    c1st
    cfv
    #
    ccom
    #
    cX
    c2nd
    cfv
    #
    cY
    c2nd
    cfv
    #
    cU
    csca
    cfv
    #
    cplusg
    cfv
    #
    co
    #
    cop
    #
    @2
    @6
    @0
    cX
    cW
    cK
    cltrn
    cfv
    cfv
    #
    cW
    cK
    ctendo
    cfv
    cfv
    #
    cxp
    #
    wcel
    cY
    @19
    wcel
    @7
    @16
    wceq
    @0
    @1
    @5
    simp1
    #
    @6
    @2
    @19
    cX
    @0
    @1
    @2
    @19
    wss
    @5
    @0
    @1
    wa
    @2
    cU
    cbs
    cfv
    #
    @19
    cA
    cQ
    cU
    cH
    cI
    cK
    c.le
    @21
    cW
    dicvaddcl.l
    dicvaddcl.a
    dicvaddcl.h
    dicvaddcl.i
    dicvaddcl.u
    @21
    eqid
    #
    dicssdvh
    @0
    @19
    @21
    wceq
    @1
    @0
    @21
    @19
    @17
    cU
    @18
    cH
    cK
    @21
    cW
    chlt
    dicvaddcl.h
    @17
    eqid
    #
    @18
    eqid
    #
    dicvaddcl.u
    @22
    dvhvbase
    eqcomd
    adantr
    sseqtr4d
    3adant3
    #
    @0
    @1
    @3
    @4
    simp3l
    sseldd
    @6
    @2
    @19
    cY
    @25
    @0
    @1
    @3
    @4
    simp3r
    sseldd
    @13
    c.pl
    @14
    @17
    cU
    @18
    cX
    cY
    cH
    cK
    cW
    dicvaddcl.h
    @23
    @24
    dicvaddcl.u
    @13
    eqid
    #
    dicvaddcl.p
    @14
    eqid
    #
    dvhvadd
    syl12anc
    @6
    @16
    @2
    wcel
    #
    @10
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
    @17
    crio
    #
    @15
    cfv
    #
    wceq
    #
    @15
    @18
    wcel
    #
    @6
    @31
    @11
    @12
    vs
    vt
    @18
    @18
    vh
    @17
    vh
    cv
    #
    vs
    cv
    cfv
    @35
    vt
    cv
    cfv
    ccom
    cmpt
    cmpt2
    #
    co
    #
    cfv
    #
    @31
    @11
    cfv
    #
    @31
    @12
    cfv
    #
    ccom
    #
    @32
    @10
    @6
    @11
    @18
    wcel
    #
    @12
    @18
    wcel
    #
    @31
    @17
    wcel
    #
    @38
    @41
    wceq
    @0
    @1
    @3
    @42
    @4
    cA
    cQ
    @18
    cH
    cI
    cK
    c.le
    cW
    cX
    dicvaddcl.l
    dicvaddcl.a
    dicvaddcl.h
    @24
    dicvaddcl.i
    dicelval2nd
    3adant3r
    #
    @0
    @1
    @4
    @43
    @3
    cA
    cQ
    @18
    cH
    cI
    cK
    c.le
    cW
    cY
    dicvaddcl.l
    dicvaddcl.a
    dicvaddcl.h
    @24
    dicvaddcl.i
    dicelval2nd
    3adant3l
    #
    @6
    @0
    @30
    cA
    wcel
    @30
    cW
    c.le
    wbr
    wn
    wa
    #
    @1
    @44
    @20
    @0
    @1
    @47
    @5
    cA
    cH
    cK
    c.le
    @29
    cW
    dicvaddcl.l
    @29
    eqid
    dicvaddcl.a
    dicvaddcl.h
    lhpocnel
    3ad2ant1
    @0
    @1
    @5
    simp2
    cA
    @30
    cQ
    @17
    vg
    @31
    cH
    cK
    c.le
    cW
    dicvaddcl.l
    dicvaddcl.a
    dicvaddcl.h
    @23
    @31
    eqid
    ltrniotacl
    syl3anc
    vt
    @36
    @17
    @11
    vh
    @18
    @31
    cK
    @12
    cW
    vs
    @23
    @36
    eqid
    #
    tendospdi2
    syl3anc
    @6
    @31
    @15
    @37
    @6
    @14
    @36
    @11
    @12
    @0
    @1
    @14
    @36
    wceq
    @5
    vt
    @36
    @14
    @17
    cU
    vh
    @18
    @13
    cH
    cK
    chlt
    cW
    vs
    dicvaddcl.h
    @23
    @24
    dicvaddcl.u
    @26
    @48
    @27
    dvhfplusr
    3ad2ant1
    oveqd
    #
    fveq1d
    @6
    @8
    @39
    @9
    @40
    @0
    @1
    @3
    @8
    @39
    wceq
    @4
    cA
    @30
    cQ
    @17
    vg
    cH
    cI
    cK
    c.le
    chlt
    cW
    cX
    dicvaddcl.l
    dicvaddcl.a
    dicvaddcl.h
    @30
    eqid
    #
    @23
    dicvaddcl.i
    dicelval1sta
    3adant3r
    @0
    @1
    @4
    @9
    @40
    wceq
    @3
    cA
    @30
    cQ
    @17
    vg
    cH
    cI
    cK
    c.le
    chlt
    cW
    cY
    dicvaddcl.l
    dicvaddcl.a
    dicvaddcl.h
    @50
    @23
    dicvaddcl.i
    dicelval1sta
    3adant3l
    coeq12d
    3eqtr4rd
    @6
    @15
    @37
    @18
    @49
    @6
    @0
    @42
    @43
    @37
    @18
    wcel
    @20
    @45
    @46
    vt
    @36
    @17
    @11
    vh
    @18
    cH
    cK
    @12
    cW
    vs
    dicvaddcl.h
    @23
    @24
    @48
    tendoplcl
    syl3anc
    eqeltrd
    @0
    @1
    @28
    @33
    @34
    wa
    wb
    @5
    cA
    @30
    cQ
    @15
    @17
    vg
    @18
    @10
    cH
    cI
    cK
    c.le
    chlt
    cW
    dicvaddcl.l
    dicvaddcl.a
    dicvaddcl.h
    @50
    @23
    @24
    dicvaddcl.i
    @8
    @9
    cX
    c1st
    fvex
    cY
    c1st
    fvex
    coex
    @11
    @12
    @14
    ovex
    dicopelval
    3adant3
    mpbir2and
    eqeltrd
end
