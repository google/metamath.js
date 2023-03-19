include "cuz.mm"
include "cfv.mm"
include "wfn.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "wrel.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "com.mm"
include "wrex.mm"
include "crn.mm"
include "eleq2i.mm"
include "wb.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmpt2.mm"
include "crdg.mm"
include "cres.mm"
include "frfnom.mm"
include "fneq1i.mm"
include "mpbir.mm"
include "fvelrnb.mm"
include "ax-mp.mm"
include "bitri.mm"
include "c2nd.mm"
include "om2uzrdg.mm"
include "om2uzuzi.mm"
include "fvex.mm"
include "opelxpi.mm"
include "sylancl.mm"
include "eqeltrd.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "rexlimiv.mm"
include "sylbi.mm"
include "ssriv.mm"
include "xpss.mm"
include "sstri.mm"
include "df-rel.mm"
include "ccnv.mm"
include "eqeq2.mm"
include "imbi2d.mm"
include "albidv.mm"
include "spcev.mm"
include "wa.mm"
include "eqeq1d.mm"
include "opth1.mm"
include "syl6bi.mm"
include "wf1o.mm"
include "om2uzf1oi.mm"
include "f1ocnvfv.mm"
include "mpan.mm"
include "syld.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "syl6.mm"
include "imp.mm"
include "vex.mm"
include "op2ndd.mm"
include "adantl.mm"
include "eqtr2d.mm"
include "rexlimiva.mm"
include "mpg.mm"
include "ax-gen.mm"
include "dffun5.mm"
include "mpbir2an.mm"
include "dmss.mm"
include "dmxpss.mm"
include "uzrdglem.mm"
include "syl6eleqr.mm"
include "opeldm.mm"
include "syl.mm"
include "eqssi.mm"
include "df-fn.mm"

theorem uzrdgfni
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let vz: setvar z
  let vw: setvar w
  let cB: class B
  let vv: setvar v
  assume om2uz.1: |- C e. ZZ
  assume om2uz.2: |- G = ( rec ( ( x e. _V |-> ( x + 1 ) ) , C ) |` _om )
  assume uzrdg.1: |- A e. _V
  assume uzrdg.2: |- R = ( rec ( ( x e. _V , y e. _V |-> <. ( x + 1 ) , ( x F y ) >. ) , <. C , A >. ) |` _om )
  assume uzrdg.3: |- S = ran R

  disjoint A y
  disjoint x y
  disjoint C x
  disjoint C y
  disjoint G y
  disjoint F x
  disjoint F y
  disjoint y z
  disjoint A z
  disjoint w z
  disjoint B w
  disjoint B z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint C v
  disjoint w x
  disjoint w y
  disjoint C w
  disjoint x z
  disjoint C z
  disjoint G v
  disjoint G w
  disjoint G z
  disjoint F w
  disjoint F z
  disjoint R v
  disjoint R w
  disjoint R z
  disjoint S v
  disjoint S w
  disjoint S z
  assert |- S Fn ( ZZ>= ` C )

  proof
    cS
    cC
    cuz
    cfv
    #
    wfn
    cS
    wfun
    #
    cS
    cdm
    #
    @0
    wceq
    @1
    cS
    wrel
    #
    vv
    cv
    #
    vz
    cv
    #
    cop
    #
    cS
    wcel
    #
    @5
    vw
    cv
    #
    wceq
    #
    wi
    #
    vz
    wal
    #
    vw
    wex
    #
    vv
    wal
    @3
    cS
    cvv
    cvv
    cxp
    #
    wss
    cS
    @0
    cvv
    cxp
    #
    @13
    vz
    cS
    @14
    @5
    cS
    wcel
    #
    @8
    cR
    cfv
    #
    @5
    wceq
    #
    vw
    com
    wrex
    #
    @5
    @14
    wcel
    #
    @15
    @5
    cR
    crn
    #
    wcel
    #
    @18
    cS
    @20
    @5
    uzrdg.3
    eleq2i
    cR
    com
    wfn
    #
    @21
    @18
    wb
    @22
    vx
    vy
    cvv
    cvv
    vx
    cv
    #
    c1
    caddc
    co
    @23
    vy
    cv
    cF
    co
    cop
    cmpt2
    #
    cC
    cA
    cop
    #
    crdg
    com
    cres
    #
    com
    wfn
    @25
    @24
    frfnom
    com
    cR
    @26
    uzrdg.2
    fneq1i
    mpbir
    #
    vw
    com
    @5
    cR
    fvelrnb
    ax-mp
    bitri
    @17
    @19
    vw
    com
    @8
    com
    wcel
    #
    @16
    @14
    wcel
    @17
    @19
    @28
    @16
    @8
    cG
    cfv
    #
    @16
    c2nd
    cfv
    #
    cop
    #
    @14
    vx
    vy
    cA
    @8
    cC
    cR
    cF
    cG
    om2uz.1
    om2uz.2
    uzrdg.1
    uzrdg.2
    om2uzrdg
    #
    @28
    @29
    @0
    wcel
    @30
    cvv
    wcel
    @31
    @14
    wcel
    vx
    @8
    cC
    cG
    om2uz.1
    om2uz.2
    om2uzuzi
    @16
    c2nd
    fvex
    #
    @29
    @30
    @0
    cvv
    opelxpi
    sylancl
    eqeltrd
    @16
    @5
    @14
    eleq1
    syl5ibcom
    rexlimiv
    sylbi
    ssriv
    #
    @0
    cvv
    xpss
    sstri
    cS
    df-rel
    mpbir
    @12
    vv
    @7
    @5
    @4
    cG
    ccnv
    cfv
    #
    cR
    cfv
    #
    c2nd
    cfv
    #
    wceq
    #
    wi
    #
    @12
    vz
    @11
    @39
    vz
    wal
    vw
    @37
    @36
    c2nd
    fvex
    #
    @8
    @37
    wceq
    #
    @10
    @39
    vz
    @41
    @9
    @38
    @7
    @8
    @37
    @5
    eqeq2
    imbi2d
    albidv
    spcev
    @7
    @16
    @6
    wceq
    #
    vw
    com
    wrex
    #
    @38
    @7
    @6
    @20
    wcel
    #
    @43
    cS
    @20
    @6
    uzrdg.3
    eleq2i
    @22
    @44
    @43
    wb
    @27
    vw
    com
    @6
    cR
    fvelrnb
    ax-mp
    bitri
    @42
    @38
    vw
    com
    @28
    @42
    wa
    @37
    @30
    @5
    @28
    @42
    @37
    @30
    wceq
    #
    @28
    @42
    @35
    @8
    wceq
    #
    @45
    @28
    @42
    @29
    @4
    wceq
    #
    @46
    @28
    @42
    @31
    @6
    wceq
    @47
    @28
    @16
    @31
    @6
    @32
    eqeq1d
    @29
    @30
    @4
    @5
    @8
    cG
    fvex
    @33
    opth1
    syl6bi
    com
    @0
    cG
    wf1o
    @28
    @47
    @46
    wi
    vx
    cC
    cG
    om2uz.1
    om2uz.2
    om2uzf1oi
    com
    @0
    @8
    @4
    cG
    f1ocnvfv
    mpan
    syld
    @46
    @36
    @16
    c2nd
    @35
    @8
    cR
    fveq2
    fveq2d
    syl6
    imp
    @42
    @30
    @5
    wceq
    @28
    @4
    @5
    @16
    vv
    vex
    #
    vz
    vex
    op2ndd
    adantl
    eqtr2d
    rexlimiva
    sylbi
    mpg
    ax-gen
    vv
    vz
    vw
    cS
    dffun5
    mpbir2an
    @2
    @0
    @2
    @14
    cdm
    #
    @0
    cS
    @14
    wss
    @2
    @49
    wss
    @34
    cS
    @14
    dmss
    ax-mp
    @0
    cvv
    dmxpss
    sstri
    vv
    @0
    @2
    @4
    @0
    wcel
    #
    @4
    @37
    cop
    #
    cS
    wcel
    @4
    @2
    wcel
    @50
    @51
    @20
    cS
    vx
    vy
    cA
    @4
    cC
    cR
    cF
    cG
    om2uz.1
    om2uz.2
    uzrdg.1
    uzrdg.2
    uzrdglem
    uzrdg.3
    syl6eleqr
    @4
    @37
    cS
    @48
    @40
    opeldm
    syl
    ssriv
    eqssi
    cS
    @0
    df-fn
    mpbir2an
end
