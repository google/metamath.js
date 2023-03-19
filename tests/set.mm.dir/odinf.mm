include "cgrp.mm"
include "wcel.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "w3a.mm"
include "crn.mm"
include "com.mm"
include "csdm.mm"
include "wbr.mm"
include "cfn.mm"
include "cen.mm"
include "cdom.mm"
include "wn.mm"
include "cz.mm"
include "cn.mm"
include "znnen.mm"
include "nnenom.mm"
include "entr2i.mm"
include "cvv.mm"
include "wf1o.mm"
include "wf1.mm"
include "wf.mm"
include "odf1.mm"
include "biimp3a.mm"
include "f1f.mm"
include "zex.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "fex2.mm"
include "mp3an23.mm"
include "3syl.mm"
include "f1f1orn.mm"
include "syl.mm"
include "f1oen3g.mm"
include "syl2anc.mm"
include "entr.mm"
include "sylancr.mm"
include "endom.mm"
include "domnsym.mm"
include "isfinite.mm"
include "sylnibr.mm"

theorem odinf
  let vx: setvar x
  let cA: class A
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cO: class O
  let cX: class X
  let vy: setvar y
  let vz: setvar z
  assume odf1.1: |- X = ( Base ` G )
  assume odf1.2: |- O = ( od ` G )
  assume odf1.3: |- .x. = ( .g ` G )
  assume odf1.4: |- F = ( x e. ZZ |-> ( x .x. A ) )

  disjoint A x
  disjoint G x
  disjoint O x
  disjoint .x. x
  disjoint X x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint G y
  disjoint G z
  disjoint O y
  disjoint O z
  disjoint .x. y
  disjoint .x. z
  disjoint X y
  disjoint X z
  disjoint F y
  disjoint F z
  assert |- ( ( G e. Grp /\ A e. X /\ ( O ` A ) = 0 ) -> -. ran F e. Fin )

  proof
    cG
    cgrp
    wcel
    #
    cA
    cX
    wcel
    #
    cA
    cO
    cfv
    cc0
    wceq
    #
    w3a
    #
    cF
    crn
    #
    com
    csdm
    wbr
    #
    @4
    cfn
    wcel
    @3
    com
    @4
    cen
    wbr
    #
    com
    @4
    cdom
    wbr
    @5
    wn
    @3
    com
    cz
    cen
    wbr
    cz
    @4
    cen
    wbr
    #
    @6
    cz
    cn
    com
    znnen
    nnenom
    entr2i
    @3
    cF
    cvv
    wcel
    #
    cz
    @4
    cF
    wf1o
    #
    @7
    @3
    cz
    cX
    cF
    wf1
    #
    cz
    cX
    cF
    wf
    #
    @8
    @0
    @1
    @2
    @10
    vx
    cA
    c.x
    cF
    cG
    cO
    cX
    odf1.1
    odf1.2
    odf1.3
    odf1.4
    odf1
    biimp3a
    #
    cz
    cX
    cF
    f1f
    @11
    cz
    cvv
    wcel
    cX
    cvv
    wcel
    @8
    zex
    cX
    cG
    cbs
    cfv
    cvv
    odf1.1
    cG
    cbs
    fvex
    eqeltri
    cz
    cX
    cF
    cvv
    cvv
    fex2
    mp3an23
    3syl
    @3
    @10
    @9
    @12
    cz
    cX
    cF
    f1f1orn
    syl
    cz
    @4
    cF
    cvv
    f1oen3g
    syl2anc
    com
    cz
    @4
    entr
    sylancr
    com
    @4
    endom
    com
    @4
    domnsym
    3syl
    @4
    isfinite
    sylnibr
end
