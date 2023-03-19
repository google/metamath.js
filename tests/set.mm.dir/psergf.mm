include "cn0.mm"
include "cc.mm"
include "wf.mm"
include "wcel.mm"
include "cfv.mm"
include "wa.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cmpt.mm"
include "ffvelrn.mm"
include "adantlr.mm"
include "expcl.mm"
include "adantll.mm"
include "mulcld.mm"
include "eqid.mm"
include "fmptd.mm"
include "wceq.mm"
include "pserval.mm"
include "adantl.mm"
include "feq1d.mm"
include "mpbird.mm"
include "syl2anc.mm"

theorem psergf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vn: setvar n
  let cG: class G
  let cX: class X
  let vi: setvar i
  let vk: setvar k
  let vm: setvar m
  let vs: setvar s
  let vy: setvar y
  let vj: setvar j
  let cH: class H
  let vr: setvar r
  let cN: class N
  let cR: class R
  let cY: class Y
  assume pser.g: |- G = ( x e. CC |-> ( n e. NN0 |-> ( ( A ` n ) x. ( x ^ n ) ) ) )
  assume radcnv.a: |- ( ph -> A : NN0 --> CC )
  assume psergf.x: |- ( ph -> X e. CC )

  disjoint n x
  disjoint A n
  disjoint A x
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i s
  disjoint i x
  disjoint i y
  disjoint A i
  disjoint k m
  disjoint k n
  disjoint k s
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint m n
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n s
  disjoint n y
  disjoint s x
  disjoint s y
  disjoint A s
  disjoint x y
  disjoint A y
  disjoint j m
  disjoint j s
  disjoint H j
  disjoint H m
  disjoint H s
  disjoint i j
  disjoint i ph
  disjoint j k
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph s
  disjoint X i
  disjoint X k
  disjoint X m
  disjoint X s
  disjoint X y
  disjoint j r
  disjoint j y
  disjoint G j
  disjoint k r
  disjoint G k
  disjoint m r
  disjoint G m
  disjoint r s
  disjoint r y
  disjoint G r
  disjoint G s
  disjoint G y
  disjoint N n
  disjoint N y
  disjoint R k
  disjoint R y
  disjoint Y i
  disjoint Y j
  disjoint Y k
  disjoint Y m
  assert |- ( ph -> ( G ` X ) : NN0 --> CC )

  proof
    wph
    cn0
    cc
    cA
    wf
    #
    cX
    cc
    wcel
    #
    cn0
    cc
    cX
    cG
    cfv
    #
    wf
    #
    radcnv.a
    psergf.x
    @0
    @1
    wa
    #
    @3
    cn0
    cc
    vm
    cn0
    vm
    cv
    #
    cA
    cfv
    #
    cX
    @5
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    wf
    @4
    vm
    cn0
    @8
    cc
    @9
    @4
    @5
    cn0
    wcel
    #
    wa
    @6
    @7
    @0
    @10
    @6
    cc
    wcel
    @1
    cn0
    cc
    @5
    cA
    ffvelrn
    adantlr
    @1
    @10
    @7
    cc
    wcel
    @0
    cX
    @5
    expcl
    adantll
    mulcld
    @9
    eqid
    fmptd
    @4
    cn0
    cc
    @2
    @9
    @1
    @2
    @9
    wceq
    @0
    vx
    cA
    vm
    vn
    cG
    cX
    pser.g
    pserval
    adantl
    feq1d
    mpbird
    syl2anc
end
