include "chash.mm"
include "cima.mm"
include "cfn.mm"
include "wcel.mm"
include "cn.mm"
include "wss.mm"
include "cres.mm"
include "wfo.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cpw.mm"
include "fzfi.mm"
include "pwfi.mm"
include "mpbi.mm"
include "cv.mm"
include "clt.mm"
include "wiso.mm"
include "wa.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "ssfi.mm"
include "mp2an.mm"
include "wfun.mm"
include "cdm.mm"
include "cvv.mm"
include "cn0.mm"
include "cpnf.mm"
include "csn.mm"
include "cun.mm"
include "wf.mm"
include "hashf.mm"
include "ffun.mm"
include "ax-mp.mm"
include "ssv.mm"
include "fdmi.mm"
include "sseqtr4i.mm"
include "fores.mm"
include "fofi.mm"
include "cfv.mm"
include "wral.mm"
include "wb.mm"
include "funimass4.mm"
include "w3a.mm"
include "erdszelem1.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "3ad2ant3.mm"
include "simp1.mm"
include "sylancr.mm"
include "hashnncl.mm"
include "syl.mm"
include "mpbird.mm"
include "sylbi.mm"
include "mprgbir.mm"
include "pm3.2i.mm"

theorem erdszelem2
  let vy: setvar y
  let cA: class A
  let cS: class S
  let cF: class F
  let cO: class O
  let vx: setvar x
  let cX: class X
  assume erdszelem1.1: |- S = { y e. ~P ( 1 ... A ) | ( ( F |` y ) Isom < , O ( y , ( F " y ) ) /\ A e. y ) }

  disjoint A y
  disjoint F y
  disjoint O y
  disjoint x y
  disjoint A x
  disjoint S x
  disjoint X y
  assert |- ( ( # " S ) e. Fin /\ ( # " S ) C_ NN )

  proof
    chash
    cS
    cima
    #
    cfn
    wcel
    #
    @0
    cn
    wss
    #
    cS
    cfn
    wcel
    #
    cS
    @0
    chash
    cS
    cres
    #
    wfo
    #
    @1
    c1
    cA
    cfz
    co
    #
    cpw
    #
    cfn
    wcel
    #
    cS
    @7
    wss
    @3
    @6
    cfn
    wcel
    #
    @8
    c1
    cA
    fzfi
    #
    @6
    pwfi
    mpbi
    cS
    vy
    cv
    #
    cF
    @11
    cima
    clt
    cO
    cF
    @11
    cres
    wiso
    cA
    @11
    wcel
    wa
    #
    vy
    @7
    crab
    @7
    erdszelem1.1
    @12
    vy
    @7
    ssrab2
    eqsstri
    @7
    cS
    ssfi
    mp2an
    chash
    wfun
    #
    cS
    chash
    cdm
    #
    wss
    #
    @5
    cvv
    cn0
    cpnf
    csn
    cun
    #
    chash
    wf
    @13
    hashf
    cvv
    @16
    chash
    ffun
    ax-mp
    #
    cS
    cvv
    @14
    cS
    ssv
    cvv
    @16
    chash
    hashf
    fdmi
    sseqtr4i
    #
    cS
    chash
    fores
    mp2an
    cS
    @0
    @4
    fofi
    mp2an
    @2
    vx
    cv
    #
    chash
    cfv
    cn
    wcel
    #
    vx
    cS
    @13
    @15
    @2
    @20
    vx
    cS
    wral
    wb
    @17
    @18
    vx
    cS
    cn
    chash
    funimass4
    mp2an
    @19
    cS
    wcel
    @19
    @6
    wss
    #
    @19
    cF
    @19
    cima
    clt
    cO
    cF
    @19
    cres
    wiso
    #
    cA
    @19
    wcel
    #
    w3a
    #
    @20
    vy
    cA
    cS
    cF
    cO
    @19
    erdszelem1.1
    erdszelem1
    @24
    @20
    @19
    c0
    wne
    #
    @23
    @21
    @25
    @22
    @19
    cA
    ne0i
    3ad2ant3
    @24
    @19
    cfn
    wcel
    #
    @20
    @25
    wb
    @24
    @9
    @21
    @26
    @10
    @21
    @22
    @23
    simp1
    @6
    @19
    ssfi
    sylancr
    @19
    hashnncl
    syl
    mpbird
    sylbi
    mprgbir
    pm3.2i
end
