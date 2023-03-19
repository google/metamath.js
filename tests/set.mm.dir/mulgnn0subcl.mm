include "cn0.mm"
include "wcel.mm"
include "w3a.mm"
include "cn.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "mulgnnsubcl.mm"
include "3expa.mm"
include "an32s.mm"
include "3adantl2.mm"
include "wa.mm"
include "oveq1.mm"
include "wss.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "sseldd.mm"
include "mulg0.mm"
include "syl.mm"
include "sylan9eqr.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "wo.mm"
include "simp2.mm"
include "elnn0.mm"
include "sylib.mm"
include "mpjaodan.mm"

theorem mulgnn0subcl
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let c.x: class .x.
  let cG: class G
  let cN: class N
  let cV: class V
  let cX: class X
  let c.0: class .0.
  let cI: class I
  assume mulgnnsubcl.b: |- B = ( Base ` G )
  assume mulgnnsubcl.t: |- .x. = ( .g ` G )
  assume mulgnnsubcl.p: |- .+ = ( +g ` G )
  assume mulgnnsubcl.g: |- ( ph -> G e. V )
  assume mulgnnsubcl.s: |- ( ph -> S C_ B )
  assume mulgnnsubcl.c: |- ( ( ph /\ x e. S /\ y e. S ) -> ( x .+ y ) e. S )
  assume mulgnn0subcl.z: |- .0. = ( 0g ` G )
  assume mulgnn0subcl.c: |- ( ph -> .0. e. S )

  disjoint x y
  disjoint .+ x
  disjoint .+ y
  disjoint B x
  disjoint B y
  disjoint G x
  disjoint G y
  disjoint N x
  disjoint N y
  disjoint S x
  disjoint S y
  disjoint ph x
  disjoint ph y
  disjoint .x. x
  disjoint X x
  disjoint X y
  disjoint I x
  assert |- ( ( ph /\ N e. NN0 /\ X e. S ) -> ( N .x. X ) e. S )

  proof
    wph
    cN
    cn0
    wcel
    #
    cX
    cS
    wcel
    #
    w3a
    #
    cN
    cn
    wcel
    #
    cN
    cX
    c.x
    co
    #
    cS
    wcel
    #
    cN
    cc0
    wceq
    #
    wph
    @1
    @3
    @5
    @0
    wph
    @3
    @1
    @5
    wph
    @3
    @1
    @5
    wph
    vx
    vy
    cB
    c.pl
    cS
    c.x
    cG
    cN
    cV
    cX
    mulgnnsubcl.b
    mulgnnsubcl.t
    mulgnnsubcl.p
    mulgnnsubcl.g
    mulgnnsubcl.s
    mulgnnsubcl.c
    mulgnnsubcl
    3expa
    an32s
    3adantl2
    @2
    @6
    wa
    @4
    c.0
    cS
    @6
    @2
    @4
    cc0
    cX
    c.x
    co
    #
    c.0
    cN
    cc0
    cX
    c.x
    oveq1
    @2
    cX
    cB
    wcel
    @7
    c.0
    wceq
    @2
    cS
    cB
    cX
    wph
    @0
    cS
    cB
    wss
    @1
    mulgnnsubcl.s
    3ad2ant1
    wph
    @0
    @1
    simp3
    sseldd
    cB
    c.x
    cG
    cX
    c.0
    mulgnnsubcl.b
    mulgnn0subcl.z
    mulgnnsubcl.t
    mulg0
    syl
    sylan9eqr
    @2
    c.0
    cS
    wcel
    #
    @6
    wph
    @0
    @8
    @1
    mulgnn0subcl.c
    3ad2ant1
    adantr
    eqeltrd
    @2
    @0
    @3
    @6
    wo
    wph
    @0
    @1
    simp2
    cN
    elnn0
    sylib
    mpjaodan
end
