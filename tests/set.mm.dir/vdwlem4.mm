include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cmin.mm"
include "caddc.mm"
include "cmul.mm"
include "cfv.mm"
include "cmpt.mm"
include "cmap.mm"
include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "c2.mm"
include "ad2antrr.mm"
include "cn.mm"
include "simplr.mm"
include "simpr.mm"
include "vdwlem3.mm"
include "ffvelrnd.mm"
include "eqid.mm"
include "fmptd.mm"
include "cfn.mm"
include "cvv.mm"
include "wb.mm"
include "adantr.mm"
include "ovex.mm"
include "elmapg.mm"
include "sylancl.mm"
include "mpbird.mm"

theorem vdwlem4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let cF: class F
  let cH: class H
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vz: setvar z
  let cA: class A
  let va: setvar a
  let vd: setvar d
  let vi: setvar i
  let vj: setvar j
  let cG: class G
  let cK: class K
  let cJ: class J
  let cP: class P
  let cB: class B
  let cM: class M
  let cD: class D
  let cE: class E
  let cT: class T
  assume vdwlem3.v: |- ( ph -> V e. NN )
  assume vdwlem3.w: |- ( ph -> W e. NN )
  assume vdwlem4.r: |- ( ph -> R e. Fin )
  assume vdwlem4.h: |- ( ph -> H : ( 1 ... ( W x. ( 2 x. V ) ) ) --> R )
  assume vdwlem4.f: |- F = ( x e. ( 1 ... V ) |-> ( y e. ( 1 ... W ) |-> ( H ` ( y + ( W x. ( ( x - 1 ) + V ) ) ) ) ) )

  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint R x
  disjoint R y
  disjoint H x
  disjoint H y
  disjoint W x
  disjoint W y
  disjoint V x
  disjoint V y
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint a d
  disjoint a i
  disjoint a j
  disjoint a k
  disjoint a m
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint G a
  disjoint d i
  disjoint d j
  disjoint d k
  disjoint d m
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint G d
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint G i
  disjoint j k
  disjoint j m
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint G j
  disjoint G k
  disjoint G m
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint a n
  disjoint K a
  disjoint d n
  disjoint K d
  disjoint i n
  disjoint K i
  disjoint j n
  disjoint K j
  disjoint K k
  disjoint K m
  disjoint K n
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint J i
  disjoint J j
  disjoint J m
  disjoint J x
  disjoint P d
  disjoint P i
  disjoint P x
  disjoint a ph
  disjoint d ph
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph z
  disjoint R i
  disjoint R k
  disjoint B i
  disjoint B j
  disjoint B m
  disjoint B n
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint H a
  disjoint H d
  disjoint H i
  disjoint H k
  disjoint H m
  disjoint H z
  disjoint M a
  disjoint M d
  disjoint M i
  disjoint M j
  disjoint M k
  disjoint M m
  disjoint M x
  disjoint M y
  disjoint D j
  disjoint D k
  disjoint D m
  disjoint D n
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint E i
  disjoint E j
  disjoint E m
  disjoint E n
  disjoint E x
  disjoint E y
  disjoint W i
  disjoint W j
  disjoint W k
  disjoint W m
  disjoint W z
  disjoint T a
  disjoint T d
  disjoint T i
  disjoint T x
  disjoint V k
  disjoint V m
  disjoint V z
  assert |- ( ph -> F : ( 1 ... V ) --> ( R ^m ( 1 ... W ) ) )

  proof
    wph
    vx
    c1
    cV
    cfz
    co
    #
    vy
    c1
    cW
    cfz
    co
    #
    vy
    cv
    #
    cW
    vx
    cv
    #
    c1
    cmin
    co
    cV
    caddc
    co
    cmul
    co
    caddc
    co
    #
    cH
    cfv
    #
    cmpt
    #
    cR
    @1
    cmap
    co
    #
    cF
    wph
    @3
    @0
    wcel
    #
    wa
    #
    @6
    @7
    wcel
    #
    @1
    cR
    @6
    wf
    #
    @9
    vy
    @1
    @5
    cR
    @6
    @9
    @2
    @1
    wcel
    #
    wa
    #
    c1
    cW
    c2
    cV
    cmul
    co
    cmul
    co
    cfz
    co
    #
    cR
    @4
    cH
    wph
    @14
    cR
    cH
    wf
    @8
    @12
    vdwlem4.h
    ad2antrr
    @13
    @3
    @2
    cV
    cW
    wph
    cV
    cn
    wcel
    @8
    @12
    vdwlem3.v
    ad2antrr
    wph
    cW
    cn
    wcel
    @8
    @12
    vdwlem3.w
    ad2antrr
    wph
    @8
    @12
    simplr
    @9
    @12
    simpr
    vdwlem3
    ffvelrnd
    @6
    eqid
    fmptd
    @9
    cR
    cfn
    wcel
    #
    @1
    cvv
    wcel
    @10
    @11
    wb
    wph
    @15
    @8
    vdwlem4.r
    adantr
    c1
    cW
    cfz
    ovex
    cR
    @1
    @6
    cfn
    cvv
    elmapg
    sylancl
    mpbird
    vdwlem4.f
    fmptd
end
