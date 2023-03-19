include "cmnd.mm"
include "wcel.mm"
include "wa.mm"
include "cs3.mm"
include "cgsu.mm"
include "co.mm"
include "cs1.mm"
include "cs2.mm"
include "cconcat.mm"
include "wceq.mm"
include "s1s2.mm"
include "a1i.mm"
include "oveq2d.mm"
include "cword.mm"
include "simpl.mm"
include "simprl.mm"
include "s1cld.mm"
include "simprrl.mm"
include "simprrr.mm"
include "s2cld.mm"
include "gsumccat.mm"
include "syl3anc.mm"
include "gsumws1.mm"
include "ad2antrl.mm"
include "gsumws2.mm"
include "3expb.mm"
include "adantrl.mm"
include "oveq12d.mm"
include "3eqtrd.mm"

theorem gsumws3
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let cT: class T
  let cU: class U
  let cG: class G
  assume gsumws3.0: |- B = ( Base ` G )
  assume gsumws3.1: |- .+ = ( +g ` G )


  assert |- ( ( G e. Mnd /\ ( S e. B /\ ( T e. B /\ U e. B ) ) ) -> ( G gsum <" S T U "> ) = ( S .+ ( T .+ U ) ) )

  proof
    cG
    cmnd
    wcel
    #
    cS
    cB
    wcel
    #
    cT
    cB
    wcel
    #
    cU
    cB
    wcel
    #
    wa
    #
    wa
    #
    wa
    #
    cG
    cS
    cT
    cU
    cs3
    #
    cgsu
    co
    cG
    cS
    cs1
    #
    cT
    cU
    cs2
    #
    cconcat
    co
    #
    cgsu
    co
    #
    cG
    @8
    cgsu
    co
    #
    cG
    @9
    cgsu
    co
    #
    c.pl
    co
    #
    cS
    cT
    cU
    c.pl
    co
    #
    c.pl
    co
    @6
    @7
    @10
    cG
    cgsu
    @7
    @10
    wceq
    @6
    cS
    cT
    cU
    s1s2
    a1i
    oveq2d
    @6
    @0
    @8
    cB
    cword
    #
    wcel
    @9
    @16
    wcel
    @11
    @14
    wceq
    @0
    @5
    simpl
    @6
    cS
    cB
    @0
    @1
    @4
    simprl
    s1cld
    @6
    cT
    cU
    cB
    @0
    @1
    @2
    @3
    simprrl
    @0
    @1
    @2
    @3
    simprrr
    s2cld
    cB
    c.pl
    cG
    @8
    @9
    gsumws3.0
    gsumws3.1
    gsumccat
    syl3anc
    @6
    @12
    cS
    @13
    @15
    c.pl
    @1
    @12
    cS
    wceq
    @0
    @4
    cB
    cS
    cG
    gsumws3.0
    gsumws1
    ad2antrl
    @0
    @4
    @13
    @15
    wceq
    #
    @1
    @0
    @2
    @3
    @17
    cB
    c.pl
    cT
    cU
    cG
    gsumws3.0
    gsumws3.1
    gsumws2
    3expb
    adantrl
    oveq12d
    3eqtrd
end
