include "cgrp.mm"
include "wcel.mm"
include "csgrp.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "wral.mm"
include "dfgrp2.mm"
include "cvv.mm"
include "wb.mm"
include "wi.mm"
include "ax-1.mm"
include "wn.mm"
include "cbs.mm"
include "cfv.mm"
include "c0.mm"
include "fvprc.mm"
include "eleq2i.mm"
include "eleq2.mm"
include "noel.mm"
include "pm2.21i.mm"
include "syl6bi.mm"
include "syl5bi.mm"
include "syl.mm"
include "pm2.61i.mm"
include "a1d.mm"
include "rexlimiv.mm"
include "issgrpv.mm"
include "pm5.32ri.mm"
include "bitri.mm"

theorem dfgrp2e
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let c.pl: class .+
  let vi: setvar i
  let vn: setvar n
  let cG: class G
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume dfgrp2.b: |- B = ( Base ` G )
  assume dfgrp2.p: |- .+ = ( +g ` G )

  disjoint B i
  disjoint B n
  disjoint B x
  disjoint i n
  disjoint i x
  disjoint n x
  disjoint G i
  disjoint G n
  disjoint G x
  disjoint .+ i
  disjoint .+ n
  disjoint .+ x
  disjoint B y
  disjoint B z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint G y
  disjoint G z
  disjoint .+ y
  disjoint .+ z
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint a b
  disjoint a c
  disjoint a i
  disjoint a n
  disjoint a x
  disjoint b c
  disjoint b i
  disjoint b n
  disjoint b x
  disjoint c i
  disjoint c n
  disjoint c x
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint .+ a
  disjoint .+ b
  disjoint .+ c
  assert |- ( G e. Grp <-> ( A. x e. B A. y e. B ( ( x .+ y ) e. B /\ A. z e. B ( ( x .+ y ) .+ z ) = ( x .+ ( y .+ z ) ) ) /\ E. n e. B A. x e. B ( ( n .+ x ) = x /\ E. i e. B ( i .+ x ) = n ) ) )

  proof
    cG
    cgrp
    wcel
    cG
    csgrp
    wcel
    #
    vn
    cv
    #
    vx
    cv
    #
    c.pl
    co
    @2
    wceq
    vi
    cv
    @2
    c.pl
    co
    @1
    wceq
    vi
    cB
    wrex
    wa
    vx
    cB
    wral
    #
    vn
    cB
    wrex
    #
    wa
    @2
    vy
    cv
    #
    c.pl
    co
    #
    cB
    wcel
    @6
    vz
    cv
    #
    c.pl
    co
    @2
    @5
    @7
    c.pl
    co
    c.pl
    co
    wceq
    vz
    cB
    wral
    wa
    vy
    cB
    wral
    vx
    cB
    wral
    #
    @4
    wa
    vx
    cB
    c.pl
    vi
    vn
    cG
    dfgrp2.b
    dfgrp2.p
    dfgrp2
    @4
    @0
    @8
    @4
    cG
    cvv
    wcel
    #
    @0
    @8
    wb
    @3
    @9
    vn
    cB
    @1
    cB
    wcel
    #
    @9
    @3
    @9
    @10
    @9
    wi
    #
    @9
    @10
    ax-1
    @9
    wn
    cG
    cbs
    cfv
    #
    c0
    wceq
    #
    @11
    cG
    cbs
    fvprc
    @10
    @1
    @12
    wcel
    #
    @13
    @9
    cB
    @12
    @1
    dfgrp2.b
    eleq2i
    @13
    @14
    @1
    c0
    wcel
    #
    @9
    @12
    c0
    @1
    eleq2
    @15
    @9
    @1
    noel
    pm2.21i
    syl6bi
    syl5bi
    syl
    pm2.61i
    a1d
    rexlimiv
    vx
    vy
    vz
    cB
    cG
    cvv
    c.pl
    dfgrp2.b
    dfgrp2.p
    issgrpv
    syl
    pm5.32ri
    bitri
end
