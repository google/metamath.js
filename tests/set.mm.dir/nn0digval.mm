include "cn.mm"
include "wcel.mm"
include "cn0.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "w3a.mm"
include "cdig.mm"
include "cfv.mm"
include "cneg.mm"
include "cexp.mm"
include "cmul.mm"
include "cfl.mm"
include "cmo.mm"
include "cdiv.mm"
include "cz.mm"
include "wceq.mm"
include "nn0z.mm"
include "digval.mm"
include "syl3an2.mm"
include "c1.mm"
include "wa.mm"
include "cc.mm"
include "nncn.mm"
include "anim1i.mm"
include "expneg.mm"
include "syl.mm"
include "3adant3.mm"
include "oveq1d.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "elrege0.mm"
include "recn.mm"
include "adantr.mm"
include "sylbi.mm"
include "3ad2ant3.mm"
include "expcl.mm"
include "3ad2ant1.mm"
include "wne.mm"
include "nnne0.mm"
include "3ad2ant2.mm"
include "expne0d.mm"
include "divrec2d.mm"
include "eqtr4d.mm"
include "fveq2d.mm"
include "eqtrd.mm"

theorem nn0digval
  let cB: class B
  let cR: class R
  let cK: class K
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( B e. NN /\ K e. NN0 /\ R e. ( 0 [,) +oo ) ) -> ( K ( digit ` B ) R ) = ( ( |_ ` ( R / ( B ^ K ) ) ) mod B ) )

  proof
    cB
    cn
    wcel
    #
    cK
    cn0
    wcel
    #
    cR
    cc0
    cpnf
    cico
    co
    wcel
    #
    w3a
    #
    cK
    cR
    cB
    cdig
    cfv
    co
    #
    cB
    cK
    cneg
    cexp
    co
    #
    cR
    cmul
    co
    #
    cfl
    cfv
    #
    cB
    cmo
    co
    #
    cR
    cB
    cK
    cexp
    co
    #
    cdiv
    co
    #
    cfl
    cfv
    #
    cB
    cmo
    co
    @1
    @0
    cK
    cz
    wcel
    #
    @2
    @4
    @8
    wceq
    cK
    nn0z
    #
    cB
    cR
    cK
    digval
    syl3an2
    @3
    @7
    @11
    cB
    cmo
    @3
    @6
    @10
    cfl
    @3
    @6
    c1
    @9
    cdiv
    co
    #
    cR
    cmul
    co
    @10
    @3
    @5
    @14
    cR
    cmul
    @0
    @1
    @5
    @14
    wceq
    #
    @2
    @0
    @1
    wa
    cB
    cc
    wcel
    #
    @1
    wa
    #
    @15
    @0
    @16
    @1
    cB
    nncn
    #
    anim1i
    #
    cB
    cK
    expneg
    syl
    3adant3
    oveq1d
    @3
    cR
    @9
    @2
    @0
    cR
    cc
    wcel
    #
    @1
    @2
    cR
    cr
    wcel
    #
    cc0
    cR
    cle
    wbr
    #
    wa
    @20
    cR
    elrege0
    @21
    @20
    @22
    cR
    recn
    adantr
    sylbi
    3ad2ant3
    @3
    @17
    @9
    cc
    wcel
    @0
    @1
    @17
    @2
    @19
    3adant3
    cB
    cK
    expcl
    syl
    @3
    cB
    cK
    @0
    @1
    @16
    @2
    @18
    3ad2ant1
    @0
    @1
    cB
    cc0
    wne
    @2
    cB
    nnne0
    3ad2ant1
    @1
    @0
    @12
    @2
    @13
    3ad2ant2
    expne0d
    divrec2d
    eqtr4d
    fveq2d
    oveq1d
    eqtrd
end
