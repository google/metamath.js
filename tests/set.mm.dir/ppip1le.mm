include "cr.mm"
include "wcel.mm"
include "cfl.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cppi.mm"
include "cle.mm"
include "cz.mm"
include "wbr.mm"
include "flcl.mm"
include "cprime.mm"
include "wa.mm"
include "wceq.mm"
include "cn0.mm"
include "zre.mm"
include "peano2re.mm"
include "syl.mm"
include "adantr.mm"
include "ppicl.mm"
include "nn0red.mm"
include "ppiprm.mm"
include "eqle.mm"
include "syl2anc.mm"
include "wn.mm"
include "ppinprm.mm"
include "lep1d.mm"
include "eqbrtrd.mm"
include "pm2.61dan.mm"
include "1z.mm"
include "fladdz.mm"
include "mpan2.mm"
include "fveq2d.mm"
include "ppifl.mm"
include "eqtr3d.mm"
include "oveq1d.mm"
include "3brtr3d.mm"

theorem ppip1le
  let cA: class A


  assert |- ( A e. RR -> ( ppi ` ( A + 1 ) ) <_ ( ( ppi ` A ) + 1 ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    cppi
    cfv
    #
    @1
    cppi
    cfv
    #
    c1
    caddc
    co
    #
    cA
    c1
    caddc
    co
    #
    cppi
    cfv
    #
    cA
    cppi
    cfv
    #
    c1
    caddc
    co
    cle
    @0
    @1
    cz
    wcel
    #
    @3
    @5
    cle
    wbr
    #
    cA
    flcl
    @9
    @2
    cprime
    wcel
    #
    @10
    @9
    @11
    wa
    #
    @3
    cr
    wcel
    @3
    @5
    wceq
    @10
    @12
    @3
    @12
    @2
    cr
    wcel
    #
    @3
    cn0
    wcel
    @9
    @13
    @11
    @9
    @1
    cr
    wcel
    #
    @13
    @1
    zre
    #
    @1
    peano2re
    syl
    adantr
    @2
    ppicl
    syl
    nn0red
    @1
    ppiprm
    @3
    @5
    eqle
    syl2anc
    @9
    @11
    wn
    #
    wa
    #
    @3
    @4
    @5
    cle
    @1
    ppinprm
    @17
    @4
    @9
    @4
    cr
    wcel
    @16
    @9
    @4
    @9
    @14
    @4
    cn0
    wcel
    @15
    @1
    ppicl
    syl
    nn0red
    adantr
    lep1d
    eqbrtrd
    pm2.61dan
    syl
    @0
    @6
    cfl
    cfv
    #
    cppi
    cfv
    #
    @3
    @7
    @0
    @18
    @2
    cppi
    @0
    c1
    cz
    wcel
    @18
    @2
    wceq
    1z
    cA
    c1
    fladdz
    mpan2
    fveq2d
    @0
    @6
    cr
    wcel
    @19
    @7
    wceq
    cA
    peano2re
    @6
    ppifl
    syl
    eqtr3d
    @0
    @4
    @8
    c1
    caddc
    cA
    ppifl
    oveq1d
    3brtr3d
end
