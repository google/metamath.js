include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "w3a.mm"
include "csubg.mm"
include "cfv.mm"
include "lidlsubg.mm"
include "3adant3.mm"
include "simp3l.mm"
include "simp3r.mm"
include "subgsubcl.mm"
include "syl3anc.mm"
include "3expa.mm"

theorem lidlsubcl
  let cR: class R
  let cU: class U
  let cI: class I
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume lidlcl.u: |- U = ( LIdeal ` R )
  assume lidlsubcl.m: |- .- = ( -g ` R )


  assert |- ( ( ( R e. Ring /\ I e. U ) /\ ( X e. I /\ Y e. I ) ) -> ( X .- Y ) e. I )

  proof
    cR
    crg
    wcel
    #
    cI
    cU
    wcel
    #
    cX
    cI
    wcel
    #
    cY
    cI
    wcel
    #
    wa
    #
    cX
    cY
    c.mi
    co
    cI
    wcel
    #
    @0
    @1
    @4
    w3a
    cI
    cR
    csubg
    cfv
    wcel
    #
    @2
    @3
    @5
    @0
    @1
    @6
    @4
    cR
    cU
    cI
    lidlcl.u
    lidlsubg
    3adant3
    @0
    @1
    @2
    @3
    simp3l
    @0
    @1
    @2
    @3
    simp3r
    cI
    cR
    c.mi
    cX
    cY
    lidlsubcl.m
    subgsubcl
    syl3anc
    3expa
end
