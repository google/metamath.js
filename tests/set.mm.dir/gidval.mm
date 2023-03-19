include "wcel.mm"
include "cvv.mm"
include "cgi.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "crio.mm"
include "elex.mm"
include "crn.mm"
include "rneq.mm"
include "syl6eqr.mm"
include "oveq.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "raleqbidv.mm"
include "riotaeqbidv.mm"
include "df-gid.mm"
include "riotaex.mm"
include "fvmpt.mm"
include "syl.mm"

theorem gidval
  let vx: setvar x
  let vu: setvar u
  let cG: class G
  let cV: class V
  let cX: class X
  let vg: setvar g
  assume gidval.1: |- X = ran G

  disjoint u x
  disjoint G u
  disjoint G x
  disjoint X u
  disjoint X x
  disjoint g u
  disjoint g x
  disjoint G g
  disjoint X g
  assert |- ( G e. V -> ( GId ` G ) = ( iota_ u e. X A. x e. X ( ( u G x ) = x /\ ( x G u ) = x ) ) )

  proof
    cG
    cV
    wcel
    cG
    cvv
    wcel
    cG
    cgi
    cfv
    vu
    cv
    #
    vx
    cv
    #
    cG
    co
    #
    @1
    wceq
    #
    @1
    @0
    cG
    co
    #
    @1
    wceq
    #
    wa
    #
    vx
    cX
    wral
    #
    vu
    cX
    crio
    #
    wceq
    cG
    cV
    elex
    vg
    cG
    @0
    @1
    vg
    cv
    #
    co
    #
    @1
    wceq
    #
    @1
    @0
    @9
    co
    #
    @1
    wceq
    #
    wa
    #
    vx
    @9
    crn
    #
    wral
    #
    vu
    @15
    crio
    @8
    cvv
    cgi
    @9
    cG
    wceq
    #
    @16
    @7
    vu
    @15
    cX
    @17
    @15
    cG
    crn
    cX
    @9
    cG
    rneq
    gidval.1
    syl6eqr
    #
    @17
    @14
    @6
    vx
    @15
    cX
    @18
    @17
    @11
    @3
    @13
    @5
    @17
    @10
    @2
    @1
    @0
    @1
    @9
    cG
    oveq
    eqeq1d
    @17
    @12
    @4
    @1
    @1
    @0
    @9
    cG
    oveq
    eqeq1d
    anbi12d
    raleqbidv
    riotaeqbidv
    vx
    vu
    vg
    df-gid
    @7
    vu
    cX
    riotaex
    fvmpt
    syl
end
