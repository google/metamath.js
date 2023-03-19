include "cmnd.mm"
include "wcel.mm"
include "cword.mm"
include "w3a.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "cgsu.mm"
include "wceq.mm"
include "s1cl.mm"
include "gsumccat.mm"
include "syl3an3.mm"
include "gsumws1.mm"
include "3ad2ant3.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem gsumccatsn
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cW: class W
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cX: class X
  assume gsumwcl.b: |- B = ( Base ` G )
  assume gsumccat.p: |- .+ = ( +g ` G )


  assert |- ( ( G e. Mnd /\ W e. Word B /\ Z e. B ) -> ( G gsum ( W ++ <" Z "> ) ) = ( ( G gsum W ) .+ Z ) )

  proof
    cG
    cmnd
    wcel
    #
    cW
    cB
    cword
    #
    wcel
    #
    cZ
    cB
    wcel
    #
    w3a
    #
    cG
    cW
    cZ
    cs1
    #
    cconcat
    co
    cgsu
    co
    #
    cG
    cW
    cgsu
    co
    #
    cG
    @5
    cgsu
    co
    #
    c.pl
    co
    #
    @7
    cZ
    c.pl
    co
    @3
    @0
    @2
    @5
    @1
    wcel
    @6
    @9
    wceq
    cZ
    cB
    s1cl
    cB
    c.pl
    cG
    cW
    @5
    gsumwcl.b
    gsumccat.p
    gsumccat
    syl3an3
    @4
    @8
    cZ
    @7
    c.pl
    @3
    @0
    @8
    cZ
    wceq
    @2
    cB
    cZ
    cG
    gsumwcl.b
    gsumws1
    3ad2ant3
    oveq2d
    eqtrd
end
