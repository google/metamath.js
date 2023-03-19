include "crn.mm"
include "cr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cpnf.mm"
include "wbr.mm"
include "wcel.mm"
include "cc0.mm"
include "cico.mm"
include "co.mm"
include "cn.mm"
include "wf.mm"
include "cle.mm"
include "cxp.mm"
include "cin.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "eqid.mm"
include "ovolsf.mm"
include "syl.mm"
include "frn.mm"
include "rge0ssre.mm"
include "syl6ss.mm"
include "cdm.mm"
include "c1.mm"
include "1nn.mm"
include "wceq.mm"
include "fdm.mm"
include "syl5eleqr.mm"
include "ne0i.mm"
include "dm0rn0.mm"
include "necon3bii.mm"
include "sylib.mm"
include "covol.mm"
include "cfv.mm"
include "caddc.mm"
include "icossxr.mm"
include "supxrcl.mm"
include "rpred.mm"
include "readdcld.mm"
include "rexrd.mm"
include "pnfxr.mm"
include "a1i.mm"
include "ltpnf.mm"
include "xrlelttrd.mm"
include "supxrbnd.mm"
include "syl3anc.mm"

theorem uniioombllem1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cC: class C
  let cS: class S
  let cT: class T
  let cE: class E
  let cF: class F
  let cG: class G
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
  let cK: class K
  let cM: class M
  let cH: class H
  let cJ: class J
  let cN: class N
  assume uniioombl.1: |- ( ph -> F : NN --> ( <_ i^i ( RR X. RR ) ) )
  assume uniioombl.2: |- ( ph -> Disj_ x e. NN ( (,) ` ( F ` x ) ) )
  assume uniioombl.3: |- S = seq 1 ( + , ( ( abs o. - ) o. F ) )
  assume uniioombl.a: |- A = U. ran ( (,) o. F )
  assume uniioombl.e: |- ( ph -> ( vol* ` E ) e. RR )
  assume uniioombl.c: |- ( ph -> C e. RR+ )
  assume uniioombl.g: |- ( ph -> G : NN --> ( <_ i^i ( RR X. RR ) ) )
  assume uniioombl.s: |- ( ph -> E C_ U. ran ( (,) o. G ) )
  assume uniioombl.t: |- T = seq 1 ( + , ( ( abs o. - ) o. G ) )
  assume uniioombl.v: |- ( ph -> sup ( ran T , RR* , < ) <_ ( ( vol* ` E ) + C ) )

  disjoint F x
  disjoint G x
  disjoint A x
  disjoint C x
  disjoint ph x
  disjoint T x
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
  disjoint A y
  disjoint A z
  disjoint C a
  disjoint C i
  disjoint C j
  disjoint C k
  disjoint C m
  disjoint C n
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
  disjoint T y
  disjoint T z
  assert |- ( ph -> sup ( ran T , RR* , < ) e. RR )

  proof
    wph
    cT
    crn
    #
    cr
    wss
    @0
    c0
    wne
    #
    @0
    cxr
    clt
    csup
    #
    cpnf
    clt
    wbr
    @2
    cr
    wcel
    wph
    @0
    cc0
    cpnf
    cico
    co
    #
    cr
    wph
    cn
    @3
    cT
    wf
    #
    @0
    @3
    wss
    wph
    cn
    cle
    cr
    cr
    cxp
    cin
    cG
    wf
    @4
    uniioombl.g
    cT
    cG
    cabs
    cmin
    ccom
    cG
    ccom
    #
    @5
    eqid
    uniioombl.t
    ovolsf
    syl
    #
    cn
    @3
    cT
    frn
    syl
    #
    rge0ssre
    syl6ss
    wph
    cT
    cdm
    #
    c0
    wne
    #
    @1
    wph
    c1
    @8
    wcel
    @9
    wph
    c1
    cn
    @8
    1nn
    wph
    @4
    @8
    cn
    wceq
    @6
    cn
    @3
    cT
    fdm
    syl
    syl5eleqr
    @8
    c1
    ne0i
    syl
    @8
    c0
    @0
    c0
    cT
    dm0rn0
    necon3bii
    sylib
    wph
    @2
    cE
    covol
    cfv
    #
    cC
    caddc
    co
    #
    cpnf
    wph
    @0
    cxr
    wss
    @2
    cxr
    wcel
    wph
    @0
    @3
    cxr
    @7
    cc0
    cpnf
    icossxr
    syl6ss
    @0
    supxrcl
    syl
    wph
    @11
    wph
    @10
    cC
    uniioombl.e
    wph
    cC
    uniioombl.c
    rpred
    readdcld
    #
    rexrd
    cpnf
    cxr
    wcel
    wph
    pnfxr
    a1i
    uniioombl.v
    wph
    @11
    cr
    wcel
    @11
    cpnf
    clt
    wbr
    @12
    @11
    ltpnf
    syl
    xrlelttrd
    @0
    supxrbnd
    syl3anc
end
