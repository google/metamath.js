include "ctcl.mm"
include "cfv.mm"
include "wbr.mm"
include "wceq.mm"
include "wn.mm"
include "wfun.mm"
include "ccom.mm"
include "cdif.mm"
include "cv.mm"
include "wi.mm"
include "wal.mm"
include "weu.mm"
include "wa.mm"
include "wex.mm"
include "eqcomd.mm"
include "cdm.mm"
include "wcel.mm"
include "wb.mm"
include "funbrfvb.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "funeu.mm"
include "wsbc.mm"
include "cvv.mm"
include "fvex.mm"
include "syl6eqel.mm"
include "sbcan.mm"
include "csb.mm"
include "sbcbr2g.mm"
include "csbvarg.mm"
include "breq2d.mm"
include "bitrd.mm"
include "sbcng.mm"
include "sbcbr1g.mm"
include "breq1d.mm"
include "notbid.mm"
include "anbi12d.mm"
include "syl5bb.mm"
include "syl.mm"
include "spesbc.mm"
include "syl6bir.mm"
include "mpand.mm"
include "eupicka.mm"
include "syl6an.mm"
include "wrel.mm"
include "funrel.mm"
include "reltrclfv.mm"
include "brrelex2.mm"
include "brcog.mm"
include "alinexa.mm"
include "syl6rbbr.mm"
include "sylibd.mm"
include "brdif.mm"
include "simplbi2.mm"
include "sylsyld.mm"
include "cun.mm"
include "wss.mm"
include "trclfvdecomr.mm"
include "uncom.mm"
include "syl6eq.mm"
include "eqimss.mm"
include "ssundif.mm"
include "sylib.mm"
include "ssbrd.mm"
include "syld.mm"
include "funbrfv.mm"
include "eqcom.mm"
include "syl6ib.mm"
include "eqtr3.mm"
include "orrd.mm"

theorem frege124d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cX: class X
  let va: setvar a
  assume frege124d.f: |- ( ph -> F e. _V )
  assume frege124d.x: |- ( ph -> X e. dom F )
  assume frege124d.a: |- ( ph -> A = ( F ` X ) )
  assume frege124d.xb: |- ( ph -> X ( t+ ` F ) B )
  assume frege124d.fun: |- ( ph -> Fun F )


  assert |- ( ph -> ( A ( t+ ` F ) B \/ A = B ) )

  proof
    wph
    cA
    cB
    cF
    ctcl
    cfv
    #
    wbr
    #
    cA
    cB
    wceq
    #
    wph
    cA
    cX
    cF
    cfv
    #
    wceq
    @1
    wn
    #
    cB
    @3
    wceq
    #
    @2
    frege124d.a
    wph
    @4
    @3
    cB
    wceq
    #
    @5
    wph
    cF
    wfun
    #
    @4
    cX
    cB
    cF
    wbr
    #
    @6
    frege124d.fun
    wph
    @4
    cX
    cB
    @0
    @0
    cF
    ccom
    #
    cdif
    #
    wbr
    #
    @8
    wph
    cX
    cB
    @0
    wbr
    #
    @4
    cX
    cB
    @9
    wbr
    #
    wn
    #
    @11
    frege124d.xb
    wph
    @4
    cX
    va
    cv
    #
    cF
    wbr
    #
    @15
    cB
    @0
    wbr
    #
    wn
    #
    wi
    va
    wal
    #
    @14
    wph
    @16
    va
    weu
    #
    @4
    @16
    @18
    wa
    #
    va
    wex
    #
    @19
    wph
    @7
    cX
    cA
    cF
    wbr
    #
    @20
    frege124d.fun
    wph
    @3
    cA
    wceq
    #
    @23
    wph
    cA
    @3
    frege124d.a
    eqcomd
    wph
    @7
    cX
    cF
    cdm
    #
    wcel
    #
    @24
    @23
    wb
    frege124d.fun
    frege124d.x
    cX
    cA
    cF
    funbrfvb
    syl2anc
    mpbid
    #
    va
    cX
    cA
    cF
    funeu
    syl2anc
    wph
    @23
    @4
    @22
    @27
    wph
    @23
    @4
    wa
    #
    @21
    va
    cA
    wsbc
    #
    @22
    wph
    cA
    cvv
    wcel
    #
    @29
    @28
    wb
    wph
    cA
    @3
    cvv
    frege124d.a
    cX
    cF
    fvex
    syl6eqel
    @29
    @16
    va
    cA
    wsbc
    #
    @18
    va
    cA
    wsbc
    #
    wa
    @30
    @28
    @16
    @18
    va
    cA
    sbcan
    @30
    @31
    @23
    @32
    @4
    @30
    @31
    cX
    va
    cA
    @15
    csb
    #
    cF
    wbr
    @23
    va
    cA
    cX
    @15
    cF
    cvv
    sbcbr2g
    @30
    @33
    cA
    cX
    cF
    va
    cA
    cvv
    csbvarg
    #
    breq2d
    bitrd
    @30
    @32
    @17
    va
    cA
    wsbc
    #
    wn
    @4
    @17
    va
    cA
    cvv
    sbcng
    @30
    @35
    @1
    @30
    @35
    @33
    cB
    @0
    wbr
    @1
    va
    cA
    @15
    cB
    @0
    cvv
    sbcbr1g
    @30
    @33
    cA
    cB
    @0
    @34
    breq1d
    bitrd
    notbid
    bitrd
    anbi12d
    syl5bb
    syl
    @21
    va
    cA
    spesbc
    syl6bir
    mpand
    @16
    @18
    va
    eupicka
    syl6an
    wph
    @14
    @16
    @17
    wa
    va
    wex
    #
    wn
    @19
    wph
    @13
    @36
    wph
    @26
    cB
    cvv
    wcel
    #
    @13
    @36
    wb
    frege124d.x
    wph
    @0
    wrel
    #
    @12
    @37
    wph
    cF
    cvv
    wcel
    #
    cF
    wrel
    #
    @38
    frege124d.f
    wph
    @7
    @40
    frege124d.fun
    cF
    funrel
    syl
    cF
    cvv
    reltrclfv
    syl2anc
    frege124d.xb
    cX
    cB
    @0
    brrelex2
    syl2anc
    va
    cX
    cB
    @0
    cF
    @25
    cvv
    brcog
    syl2anc
    notbid
    @16
    @17
    va
    alinexa
    syl6rbbr
    sylibd
    @11
    @12
    @14
    cX
    cB
    @0
    @9
    brdif
    simplbi2
    sylsyld
    wph
    @10
    cF
    cX
    cB
    wph
    @0
    @9
    cF
    cun
    #
    wss
    #
    @10
    cF
    wss
    wph
    @0
    @41
    wceq
    @42
    wph
    @0
    cF
    @9
    cun
    #
    @41
    wph
    @39
    @0
    @43
    wceq
    frege124d.f
    cF
    cvv
    trclfvdecomr
    syl
    cF
    @9
    uncom
    syl6eq
    @0
    @41
    eqimss
    syl
    @0
    @9
    cF
    ssundif
    sylib
    ssbrd
    syld
    cX
    cB
    cF
    funbrfv
    sylsyld
    @3
    cB
    eqcom
    syl6ib
    cA
    cB
    @3
    eqtr3
    syl6an
    orrd
end
