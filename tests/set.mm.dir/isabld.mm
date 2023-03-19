include "cgrp.mm"
include "wcel.mm"
include "ccmn.mm"
include "cabl.mm"
include "cmnd.mm"
include "grpmnd.mm"
include "syl.mm"
include "iscmnd.mm"
include "isabl.mm"
include "sylanbrc.mm"

theorem isabld
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let cG: class G
  assume isabld.b: |- ( ph -> B = ( Base ` G ) )
  assume isabld.p: |- ( ph -> .+ = ( +g ` G ) )
  assume isabld.g: |- ( ph -> G e. Grp )
  assume isabld.c: |- ( ( ph /\ x e. B /\ y e. B ) -> ( x .+ y ) = ( y .+ x ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint G x
  disjoint G y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> G e. Abel )

  proof
    wph
    cG
    cgrp
    wcel
    #
    cG
    ccmn
    wcel
    cG
    cabl
    wcel
    isabld.g
    wph
    vx
    vy
    cB
    c.pl
    cG
    isabld.b
    isabld.p
    wph
    @0
    cG
    cmnd
    wcel
    isabld.g
    cG
    grpmnd
    syl
    isabld.c
    iscmnd
    cG
    isabl
    sylanbrc
end
