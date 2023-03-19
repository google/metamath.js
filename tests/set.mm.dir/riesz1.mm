include "clf.mm"
include "wcel.mm"
include "ccnfn.mm"
include "cnmf.mm"
include "cfv.mm"
include "cr.mm"
include "cv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "wrex.mm"
include "lnfncnbd.mm"
include "wa.mm"
include "cin.mm"
include "elin.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "cif.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "rexralbidv.mm"
include "inss1.mm"
include "0lnfn.mm"
include "0cnfn.mm"
include "mpbir2an.mm"
include "elimel.mm"
include "sselii.mm"
include "inss2.mm"
include "riesz3i.mm"
include "dedth.mm"
include "sylbir.mm"
include "ex.mm"
include "cabs.mm"
include "cno.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "normcl.mm"
include "adantl.mm"
include "wi.mm"
include "fveq2.mm"
include "bcs.mm"
include "cc.mm"
include "recn.mm"
include "mulcom.mm"
include "syl2an.mm"
include "breqtrd.mm"
include "adantll.mm"
include "adantr.mm"
include "eqbrtrd.mm"
include "an32s.mm"
include "ralimdva.mm"
include "oveq1.mm"
include "breq2d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl6an.mm"
include "rexlimdva.mm"
include "lnfncon.mm"
include "sylibrd.mm"
include "impbid.mm"
include "bitr3d.mm"

theorem riesz1
  let vx: setvar x
  let vy: setvar y
  let cT: class T
  let vz: setvar z

  disjoint x y
  disjoint T x
  disjoint T y
  disjoint x z
  disjoint y z
  disjoint T z
  assert |- ( T e. LinFn -> ( ( normfn ` T ) e. RR <-> E. y e. ~H A. x e. ~H ( T ` x ) = ( x .ih y ) ) )

  proof
    cT
    clf
    wcel
    #
    cT
    ccnfn
    wcel
    #
    cT
    cnmf
    cfv
    cr
    wcel
    vx
    cv
    #
    cT
    cfv
    #
    @2
    vy
    cv
    #
    csp
    co
    #
    wceq
    #
    vx
    chil
    wral
    #
    vy
    chil
    wrex
    #
    cT
    lnfncnbd
    @0
    @1
    @8
    @0
    @1
    @8
    @0
    @1
    wa
    cT
    clf
    ccnfn
    cin
    #
    wcel
    #
    @8
    cT
    clf
    ccnfn
    elin
    @10
    @8
    @2
    @10
    cT
    chil
    cc0
    csn
    cxp
    #
    cif
    #
    cfv
    #
    @5
    wceq
    #
    vx
    chil
    wral
    vy
    chil
    wrex
    cT
    @11
    cT
    @12
    wceq
    #
    @6
    @14
    vy
    vx
    chil
    chil
    @15
    @3
    @13
    @5
    @2
    cT
    @12
    fveq1
    eqeq1d
    rexralbidv
    vy
    vx
    @12
    @9
    clf
    @12
    clf
    ccnfn
    inss1
    cT
    @11
    @9
    @11
    @9
    wcel
    @11
    clf
    wcel
    @11
    ccnfn
    wcel
    0lnfn
    0cnfn
    @11
    clf
    ccnfn
    elin
    mpbir2an
    elimel
    #
    sselii
    @9
    ccnfn
    @12
    clf
    ccnfn
    inss2
    @16
    sselii
    riesz3i
    dedth
    sylbir
    ex
    @0
    @8
    @3
    cabs
    cfv
    #
    vz
    cv
    #
    @2
    cno
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    vx
    chil
    wral
    #
    vz
    cr
    wrex
    #
    @1
    @0
    @7
    @23
    vy
    chil
    @0
    @4
    chil
    wcel
    #
    wa
    #
    @4
    cno
    cfv
    #
    cr
    wcel
    #
    @7
    @17
    @26
    @19
    cmul
    co
    #
    cle
    wbr
    #
    vx
    chil
    wral
    #
    @23
    @24
    @27
    @0
    @4
    normcl
    #
    adantl
    @25
    @6
    @29
    vx
    chil
    @0
    @2
    chil
    wcel
    #
    @24
    @6
    @29
    wi
    @0
    @32
    wa
    @24
    wa
    #
    @6
    @29
    @33
    @6
    wa
    @17
    @5
    cabs
    cfv
    #
    @28
    cle
    @6
    @17
    @34
    wceq
    @33
    @3
    @5
    cabs
    fveq2
    adantl
    @33
    @34
    @28
    cle
    wbr
    #
    @6
    @32
    @24
    @35
    @0
    @32
    @24
    wa
    @34
    @19
    @26
    cmul
    co
    #
    @28
    cle
    @2
    @4
    bcs
    @32
    @19
    cr
    wcel
    #
    @27
    @36
    @28
    wceq
    #
    @24
    @2
    normcl
    @31
    @37
    @19
    cc
    wcel
    @26
    cc
    wcel
    @38
    @27
    @19
    recn
    @26
    recn
    @19
    @26
    mulcom
    syl2an
    syl2an
    breqtrd
    adantll
    adantr
    eqbrtrd
    ex
    an32s
    ralimdva
    @22
    @30
    vz
    @26
    cr
    @18
    @26
    wceq
    #
    @21
    @29
    vx
    chil
    @39
    @20
    @28
    @17
    cle
    @18
    @26
    @19
    cmul
    oveq1
    breq2d
    ralbidv
    rspcev
    syl6an
    rexlimdva
    vz
    vx
    cT
    lnfncon
    sylibrd
    impbid
    bitr3d
end
