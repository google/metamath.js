include "cmnd.mm"
include "wcel.mm"
include "w3a.mm"
include "cs2.mm"
include "cgsu.mm"
include "co.mm"
include "cs1.mm"
include "cconcat.mm"
include "wceq.mm"
include "df-s2.mm"
include "a1i.mm"
include "oveq2d.mm"
include "cword.mm"
include "id.mm"
include "s1cl.mm"
include "gsumccat.mm"
include "syl3an.mm"
include "gsumws1.mm"
include "oveqan12d.mm"
include "3adant1.mm"
include "3eqtrd.mm"

theorem gsumws2
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let cT: class T
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cW: class W
  let cX: class X
  assume gsumwcl.b: |- B = ( Base ` G )
  assume gsumccat.p: |- .+ = ( +g ` G )


  assert |- ( ( G e. Mnd /\ S e. B /\ T e. B ) -> ( G gsum <" S T "> ) = ( S .+ T ) )

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
    w3a
    #
    cG
    cS
    cT
    cs2
    #
    cgsu
    co
    cG
    cS
    cs1
    #
    cT
    cs1
    #
    cconcat
    co
    #
    cgsu
    co
    #
    cG
    @5
    cgsu
    co
    #
    cG
    @6
    cgsu
    co
    #
    c.pl
    co
    #
    cS
    cT
    c.pl
    co
    #
    @3
    @4
    @7
    cG
    cgsu
    @4
    @7
    wceq
    @3
    cS
    cT
    df-s2
    a1i
    oveq2d
    @0
    @0
    @1
    @5
    cB
    cword
    #
    wcel
    @2
    @6
    @13
    wcel
    @8
    @11
    wceq
    @0
    id
    cS
    cB
    s1cl
    cT
    cB
    s1cl
    cB
    c.pl
    cG
    @5
    @6
    gsumwcl.b
    gsumccat.p
    gsumccat
    syl3an
    @1
    @2
    @11
    @12
    wceq
    @0
    @1
    @2
    @9
    cS
    @10
    cT
    c.pl
    cB
    cS
    cG
    gsumwcl.b
    gsumws1
    cB
    cT
    cG
    gsumwcl.b
    gsumws1
    oveqan12d
    3adant1
    3eqtrd
end
