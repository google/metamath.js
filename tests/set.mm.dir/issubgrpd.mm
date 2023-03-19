include "cress.mm"
include "co.mm"
include "cgrp.mm"
include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "issubgrpd2.mm"
include "eqid.mm"
include "subggrp.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem issubgrpd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let c.pl: class .+
  let cS: class S
  let cI: class I
  let c.0: class .0.
  assume issubgrpd.s: |- ( ph -> S = ( I |`s D ) )
  assume issubgrpd.z: |- ( ph -> .0. = ( 0g ` I ) )
  assume issubgrpd.p: |- ( ph -> .+ = ( +g ` I ) )
  assume issubgrpd.ss: |- ( ph -> D C_ ( Base ` I ) )
  assume issubgrpd.zcl: |- ( ph -> .0. e. D )
  assume issubgrpd.acl: |- ( ( ph /\ x e. D /\ y e. D ) -> ( x .+ y ) e. D )
  assume issubgrpd.ncl: |- ( ( ph /\ x e. D ) -> ( ( invg ` I ) ` x ) e. D )
  assume issubgrpd.g: |- ( ph -> I e. Grp )

  disjoint x y
  disjoint .0. x
  disjoint .0. y
  disjoint D x
  disjoint D y
  disjoint I x
  disjoint I y
  disjoint .+ x
  disjoint .+ y
  disjoint ph x
  disjoint ph y
  disjoint S x
  disjoint S y
  assert |- ( ph -> S e. Grp )

  proof
    wph
    cS
    cI
    cD
    cress
    co
    #
    cgrp
    issubgrpd.s
    wph
    cD
    cI
    csubg
    cfv
    wcel
    @0
    cgrp
    wcel
    wph
    vx
    vy
    cD
    c.pl
    cS
    cI
    c.0
    issubgrpd.s
    issubgrpd.z
    issubgrpd.p
    issubgrpd.ss
    issubgrpd.zcl
    issubgrpd.acl
    issubgrpd.ncl
    issubgrpd.g
    issubgrpd2
    cD
    cI
    @0
    @0
    eqid
    subggrp
    syl
    eqeltrd
end
