include "cmnd.mm"
include "wcel.mm"
include "wa.mm"
include "cs4.mm"
include "cgsu.mm"
include "co.mm"
include "cs1.mm"
include "cs3.mm"
include "cconcat.mm"
include "wceq.mm"
include "s1s3.mm"
include "a1i.mm"
include "oveq2d.mm"
include "cword.mm"
include "simpl.mm"
include "simprl.mm"
include "s1cld.mm"
include "simprrl.mm"
include "adantl.mm"
include "simprrr.mm"
include "s3cld.mm"
include "gsumccat.mm"
include "syl3anc.mm"
include "gsumws1.mm"
include "ad2antrl.mm"
include "gsumws3.mm"
include "adantrl.mm"
include "oveq12d.mm"
include "3eqtrd.mm"

theorem gsumws4
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let cT: class T
  let cU: class U
  let cG: class G
  let cV: class V
  assume gsumws4.0: |- B = ( Base ` G )
  assume gsumws4.1: |- .+ = ( +g ` G )


  assert |- ( ( G e. Mnd /\ ( S e. B /\ ( T e. B /\ ( U e. B /\ V e. B ) ) ) ) -> ( G gsum <" S T U V "> ) = ( S .+ ( T .+ ( U .+ V ) ) ) )

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
    cV
    cB
    wcel
    #
    wa
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
    cV
    cs4
    #
    cgsu
    co
    cG
    cS
    cs1
    #
    cT
    cU
    cV
    cs3
    #
    cconcat
    co
    #
    cgsu
    co
    #
    cG
    @10
    cgsu
    co
    #
    cG
    @11
    cgsu
    co
    #
    c.pl
    co
    #
    cS
    cT
    cU
    cV
    c.pl
    co
    c.pl
    co
    #
    c.pl
    co
    @8
    @9
    @12
    cG
    cgsu
    @9
    @12
    wceq
    @8
    cS
    cT
    cU
    cV
    s1s3
    a1i
    oveq2d
    @8
    @0
    @10
    cB
    cword
    #
    wcel
    @11
    @18
    wcel
    @13
    @16
    wceq
    @0
    @7
    simpl
    @8
    cS
    cB
    @0
    @1
    @6
    simprl
    s1cld
    @8
    cT
    cU
    cV
    cB
    @0
    @1
    @2
    @5
    simprrl
    @7
    @3
    @0
    @1
    @2
    @3
    @4
    simprrl
    adantl
    @7
    @4
    @0
    @1
    @2
    @3
    @4
    simprrr
    adantl
    s3cld
    cB
    c.pl
    cG
    @10
    @11
    gsumws4.0
    gsumws4.1
    gsumccat
    syl3anc
    @8
    @14
    cS
    @15
    @17
    c.pl
    @1
    @14
    cS
    wceq
    @0
    @6
    cB
    cS
    cG
    gsumws4.0
    gsumws1
    ad2antrl
    @0
    @6
    @15
    @17
    wceq
    @1
    cB
    c.pl
    cT
    cU
    cV
    cG
    gsumws4.0
    gsumws4.1
    gsumws3
    adantrl
    oveq12d
    3eqtrd
end
