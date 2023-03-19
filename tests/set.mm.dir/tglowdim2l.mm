include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "wrex.mm"
include "w3o.mm"
include "cds.mm"
include "cfv.mm"
include "cstrkg.mm"
include "eqid.mm"
include "axtglowdim2.mm"
include "wa.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "simplr.mm"
include "simpr.mm"
include "tgcolg.mm"
include "notbid.mm"
include "rexbidva.mm"
include "mpbird.mm"

theorem tglowdim2l
  let wph: wff ph
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vz: setvar z
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  assume tglineintmo.p: |- P = ( Base ` G )
  assume tglineintmo.i: |- I = ( Itv ` G )
  assume tglineintmo.l: |- L = ( LineG ` G )
  assume tglineintmo.g: |- ( ph -> G e. TarskiG )
  assume tglowdim2l.1: |- ( ph -> G TarskiGDim>= 2 )

  disjoint a b
  disjoint a c
  disjoint G a
  disjoint b c
  disjoint G b
  disjoint G c
  disjoint I a
  disjoint I b
  disjoint I c
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint a z
  disjoint b z
  disjoint c z
  disjoint G z
  disjoint I z
  disjoint P z
  disjoint ph z
  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> E. a e. P E. b e. P E. c e. P -. ( c e. ( a L b ) \/ a = b ) )

  proof
    wph
    vc
    cv
    #
    va
    cv
    #
    vb
    cv
    #
    cL
    co
    wcel
    @1
    @2
    wceq
    wo
    #
    wn
    #
    vc
    cP
    wrex
    #
    vb
    cP
    wrex
    #
    va
    cP
    wrex
    @0
    @1
    @2
    cI
    co
    wcel
    @1
    @0
    @2
    cI
    co
    wcel
    @2
    @1
    @0
    cI
    co
    wcel
    w3o
    #
    wn
    #
    vc
    cP
    wrex
    #
    vb
    cP
    wrex
    #
    va
    cP
    wrex
    wph
    va
    vb
    vc
    cP
    cG
    cI
    cG
    cds
    cfv
    #
    cstrkg
    tglineintmo.p
    @11
    eqid
    tglineintmo.i
    tglineintmo.g
    tglowdim2l.1
    axtglowdim2
    wph
    @6
    @10
    va
    cP
    wph
    @1
    cP
    wcel
    #
    wa
    #
    @5
    @9
    vb
    cP
    @13
    @2
    cP
    wcel
    #
    wa
    #
    @4
    @8
    vc
    cP
    @15
    @0
    cP
    wcel
    #
    wa
    #
    @3
    @7
    @17
    cP
    cG
    cI
    cL
    @1
    @2
    @0
    tglineintmo.p
    tglineintmo.l
    tglineintmo.i
    wph
    cG
    cstrkg
    wcel
    @12
    @14
    @16
    tglineintmo.g
    ad3antrrr
    wph
    @12
    @14
    @16
    simpllr
    @13
    @14
    @16
    simplr
    @15
    @16
    simpr
    tgcolg
    notbid
    rexbidva
    rexbidva
    rexbidva
    mpbird
end
