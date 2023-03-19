include "cn.mm"
include "wcel.mm"
include "cz.mm"
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
include "cn0.mm"
include "digval.mm"
include "cr.mm"
include "nnre.mm"
include "3ad2ant1.mm"
include "wne.mm"
include "nnne0.mm"
include "znegcl.mm"
include "3ad2ant2.mm"
include "reexpclzd.mm"
include "cle.mm"
include "wbr.mm"
include "elrege0.mm"
include "simplbi.mm"
include "3ad2ant3.mm"
include "remulcld.mm"
include "flcld.mm"
include "simp1.mm"
include "zmodcld.mm"
include "eqeltrd.mm"

theorem digvalnn0
  let cB: class B
  let cR: class R
  let cK: class K
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( B e. NN /\ K e. ZZ /\ R e. ( 0 [,) +oo ) ) -> ( K ( digit ` B ) R ) e. NN0 )

  proof
    cB
    cn
    wcel
    #
    cK
    cz
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
    cB
    cK
    cneg
    #
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
    cn0
    cB
    cR
    cK
    digval
    @3
    @7
    cB
    @3
    @6
    @3
    @5
    cR
    @3
    cB
    @4
    @0
    @1
    cB
    cr
    wcel
    @2
    cB
    nnre
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
    @4
    cz
    wcel
    @2
    cK
    znegcl
    3ad2ant2
    reexpclzd
    @2
    @0
    cR
    cr
    wcel
    #
    @1
    @2
    @8
    cc0
    cR
    cle
    wbr
    cR
    elrege0
    simplbi
    3ad2ant3
    remulcld
    flcld
    @0
    @1
    @2
    simp1
    zmodcld
    eqeltrd
end
