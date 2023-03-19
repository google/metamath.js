include "cioo.mm"
include "ccom.mm"
include "crn.mm"
include "cuni.mm"
include "cicc.mm"
include "cdif.mm"
include "cun.mm"
include "cvol.mm"
include "cdm.mm"
include "wss.mm"
include "wceq.mm"
include "covol.mm"
include "cfv.mm"
include "cc0.mm"
include "uniiccdif.mm"
include "simpld.mm"
include "undif.mm"
include "sylib.mm"
include "wcel.mm"
include "uniioombl.mm"
include "cr.mm"
include "cn.mm"
include "cle.mm"
include "cxp.mm"
include "cin.mm"
include "wf.mm"
include "ovolficcss.mm"
include "syl.mm"
include "ssdifssd.mm"
include "simprd.mm"
include "nulmbl.mm"
include "syl2anc.mm"
include "unmbl.mm"
include "eqeltrrd.mm"

theorem uniiccmbl
  let wph: wff ph
  let vx: setvar x
  let cS: class S
  let cF: class F
  let va: setvar a
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let vr: setvar r
  let vy: setvar y
  let vz: setvar z
  let vm: setvar m
  let vw: setvar w
  let cG: class G
  let cK: class K
  let cA: class A
  let cC: class C
  let cM: class M
  let cE: class E
  let cH: class H
  let cJ: class J
  let cN: class N
  let cT: class T
  assume uniioombl.1: |- ( ph -> F : NN --> ( <_ i^i ( RR X. RR ) ) )
  assume uniioombl.2: |- ( ph -> Disj_ x e. NN ( (,) ` ( F ` x ) ) )
  assume uniioombl.3: |- S = seq 1 ( + , ( ( abs o. - ) o. F ) )

  disjoint F x
  disjoint ph x
  disjoint a f
  disjoint a i
  disjoint a j
  disjoint a k
  disjoint a n
  disjoint a r
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint F a
  disjoint f i
  disjoint f j
  disjoint f k
  disjoint f n
  disjoint f r
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint i j
  disjoint i k
  disjoint i n
  disjoint i r
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint F i
  disjoint j k
  disjoint j n
  disjoint j r
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint F j
  disjoint k n
  disjoint k r
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint F r
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint a m
  disjoint a w
  disjoint G a
  disjoint i m
  disjoint i w
  disjoint G i
  disjoint j m
  disjoint j w
  disjoint G j
  disjoint k m
  disjoint k w
  disjoint G k
  disjoint m n
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint G m
  disjoint n w
  disjoint G n
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint K j
  disjoint K n
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint A a
  disjoint A j
  disjoint A k
  disjoint A m
  disjoint A n
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint C a
  disjoint C i
  disjoint C j
  disjoint C k
  disjoint C m
  disjoint C n
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint M i
  disjoint M j
  disjoint M k
  disjoint M n
  disjoint M w
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint E m
  disjoint E n
  disjoint H n
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint J n
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint N i
  disjoint N j
  disjoint N n
  disjoint N z
  disjoint S n
  disjoint S y
  disjoint a ph
  disjoint f m
  disjoint f ph
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint m r
  disjoint m ph
  disjoint n ph
  disjoint ph r
  disjoint ph y
  disjoint ph z
  disjoint T a
  disjoint T i
  disjoint T j
  disjoint T k
  disjoint T m
  disjoint T n
  disjoint T x
  disjoint T y
  disjoint T z
  assert |- ( ph -> U. ran ( [,] o. F ) e. dom vol )

  proof
    wph
    cioo
    cF
    ccom
    crn
    cuni
    #
    cicc
    cF
    ccom
    crn
    cuni
    #
    @0
    cdif
    #
    cun
    #
    @1
    cvol
    cdm
    #
    wph
    @0
    @1
    wss
    #
    @3
    @1
    wceq
    wph
    @5
    @2
    covol
    cfv
    cc0
    wceq
    #
    wph
    cF
    uniioombl.1
    uniiccdif
    #
    simpld
    @0
    @1
    undif
    sylib
    wph
    @0
    @4
    wcel
    @2
    @4
    wcel
    #
    @3
    @4
    wcel
    wph
    vx
    cS
    cF
    uniioombl.1
    uniioombl.2
    uniioombl.3
    uniioombl
    wph
    @2
    cr
    wss
    @6
    @8
    wph
    @1
    cr
    @0
    wph
    cn
    cle
    cr
    cr
    cxp
    cin
    cF
    wf
    @1
    cr
    wss
    uniioombl.1
    cF
    ovolficcss
    syl
    ssdifssd
    wph
    @5
    @6
    @7
    simprd
    @2
    nulmbl
    syl2anc
    @0
    @2
    unmbl
    syl2anc
    eqeltrrd
end
