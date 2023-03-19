include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "cfz.mm"
include "cv.mm"
include "wf1.mm"
include "crn.mm"
include "clt.mm"
include "wiso.mm"
include "wa.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cima.mm"
include "cres.mm"
include "ccnv.mm"
include "wo.mm"
include "cpw.mm"
include "wrex.mm"
include "eqid.mm"
include "erdsze2lem1.mm"
include "cn.mm"
include "wcel.mm"
include "adantr.mm"
include "cr.mm"
include "wss.mm"
include "simprl.mm"
include "simprr.mm"
include "erdsze2lem2.mm"
include "exlimddv.mm"

theorem erdsze2
  let wph: wff ph
  let cA: class A
  let cR: class R
  let cS: class S
  let cF: class F
  let vs: setvar s
  let vf: setvar f
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let cG: class G
  let cN: class N
  assume erdsze2.r: |- ( ph -> R e. NN )
  assume erdsze2.s: |- ( ph -> S e. NN )
  assume erdsze2.f: |- ( ph -> F : A -1-1-> RR )
  assume erdsze2.a: |- ( ph -> A C_ RR )
  assume erdsze2.l: |- ( ph -> ( ( R - 1 ) x. ( S - 1 ) ) < ( # ` A ) )

  disjoint A s
  disjoint F s
  disjoint R s
  disjoint S s
  disjoint ph s
  disjoint f s
  disjoint f t
  disjoint A f
  disjoint s t
  disjoint A t
  disjoint F f
  disjoint F t
  disjoint s x
  disjoint s y
  disjoint G s
  disjoint t x
  disjoint t y
  disjoint G t
  disjoint x y
  disjoint G x
  disjoint G y
  disjoint R f
  disjoint R t
  disjoint S f
  disjoint S t
  disjoint f x
  disjoint f y
  disjoint N f
  disjoint N s
  disjoint N t
  disjoint N x
  disjoint N y
  disjoint f ph
  disjoint ph t
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> E. s e. ~P A ( ( R <_ ( # ` s ) /\ ( F |` s ) Isom < , < ( s , ( F " s ) ) ) \/ ( S <_ ( # ` s ) /\ ( F |` s ) Isom < , `' < ( s , ( F " s ) ) ) ) )

  proof
    wph
    c1
    cR
    c1
    cmin
    co
    cS
    c1
    cmin
    co
    cmul
    co
    #
    c1
    caddc
    co
    cfz
    co
    #
    cA
    vf
    cv
    #
    wf1
    #
    @1
    @2
    crn
    clt
    clt
    @2
    wiso
    #
    wa
    #
    cR
    vs
    cv
    #
    chash
    cfv
    #
    cle
    wbr
    @6
    cF
    @6
    cima
    #
    clt
    clt
    cF
    @6
    cres
    #
    wiso
    wa
    cS
    @7
    cle
    wbr
    @6
    @8
    clt
    clt
    ccnv
    @9
    wiso
    wa
    wo
    vs
    cA
    cpw
    wrex
    vf
    wph
    cA
    cR
    cS
    vf
    cF
    @0
    erdsze2.r
    erdsze2.s
    erdsze2.f
    erdsze2.a
    @0
    eqid
    #
    erdsze2.l
    erdsze2lem1
    wph
    @5
    wa
    cA
    cR
    cS
    cF
    @2
    @0
    vs
    wph
    cR
    cn
    wcel
    @5
    erdsze2.r
    adantr
    wph
    cS
    cn
    wcel
    @5
    erdsze2.s
    adantr
    wph
    cA
    cr
    cF
    wf1
    @5
    erdsze2.f
    adantr
    wph
    cA
    cr
    wss
    @5
    erdsze2.a
    adantr
    @10
    wph
    @0
    cA
    chash
    cfv
    clt
    wbr
    @5
    erdsze2.l
    adantr
    wph
    @3
    @4
    simprl
    wph
    @3
    @4
    simprr
    erdsze2lem2
    exlimddv
end
