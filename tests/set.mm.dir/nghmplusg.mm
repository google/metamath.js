include "cabl.mm"
include "wcel.mm"
include "cnghm.mm"
include "co.mm"
include "w3a.mm"
include "cngp.mm"
include "cof.mm"
include "cghm.mm"
include "cnmo.mm"
include "cfv.mm"
include "caddc.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "nghmrcl1.mm"
include "3ad2ant2.mm"
include "nghmrcl2.mm"
include "id.mm"
include "nghmghm.mm"
include "ghmplusg.mm"
include "syl3an.mm"
include "eqid.mm"
include "nghmcl.mm"
include "3ad2ant3.mm"
include "readdcld.mm"
include "nmotri.mm"
include "bddnghm.mm"
include "syl32anc.mm"

theorem nghmplusg
  let c.pl: class .+
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  assume nghmplusg.p: |- .+ = ( +g ` T )


  assert |- ( ( T e. Abel /\ F e. ( S NGHom T ) /\ G e. ( S NGHom T ) ) -> ( F oF .+ G ) e. ( S NGHom T ) )

  proof
    cT
    cabl
    wcel
    #
    cF
    cS
    cT
    cnghm
    co
    #
    wcel
    #
    cG
    @1
    wcel
    #
    w3a
    #
    cS
    cngp
    wcel
    #
    cT
    cngp
    wcel
    #
    cF
    cG
    c.pl
    cof
    co
    #
    cS
    cT
    cghm
    co
    #
    wcel
    #
    cF
    cS
    cT
    cnmo
    co
    #
    cfv
    #
    cG
    @10
    cfv
    #
    caddc
    co
    #
    cr
    wcel
    @7
    @10
    cfv
    @13
    cle
    wbr
    @7
    @1
    wcel
    @2
    @0
    @5
    @3
    cS
    cT
    cF
    nghmrcl1
    3ad2ant2
    @2
    @0
    @6
    @3
    cS
    cT
    cF
    nghmrcl2
    3ad2ant2
    @0
    @0
    @2
    cF
    @8
    wcel
    @3
    cG
    @8
    wcel
    @9
    @0
    id
    cS
    cT
    cF
    nghmghm
    cS
    cT
    cG
    nghmghm
    c.pl
    cF
    cG
    cS
    cT
    nghmplusg.p
    ghmplusg
    syl3an
    @4
    @11
    @12
    @2
    @0
    @11
    cr
    wcel
    @3
    cS
    cT
    cF
    @10
    @10
    eqid
    #
    nghmcl
    3ad2ant2
    @3
    @0
    @12
    cr
    wcel
    @2
    cS
    cT
    cG
    @10
    @14
    nghmcl
    3ad2ant3
    readdcld
    c.pl
    cS
    cT
    cF
    cG
    @10
    @14
    nghmplusg.p
    nmotri
    @13
    cS
    cT
    @7
    @10
    @14
    bddnghm
    syl32anc
end
