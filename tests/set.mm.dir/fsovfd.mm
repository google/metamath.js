include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "crab.mm"
include "cmpt.mm"
include "fsovd.mm"
include "syl5eq.mm"
include "wf.mm"
include "wss.mm"
include "ssrab2.mm"
include "a1i.mm"
include "sselpwd.mm"
include "adantr.mm"
include "eqid.mm"
include "fmptd.mm"
include "cvv.mm"
include "pwexg.mm"
include "syl.mm"
include "elmapd.mm"
include "mpbird.mm"
include "fmpt3d.mm"

theorem fsovfd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cG: class G
  let cO: class O
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  assume fsovd.fs: |- O = ( a e. _V , b e. _V |-> ( f e. ( ~P b ^m a ) |-> ( y e. b |-> { x e. a | y e. ( f ` x ) } ) ) )
  assume fsovd.a: |- ( ph -> A e. V )
  assume fsovd.b: |- ( ph -> B e. W )
  assume fsovfvd.g: |- G = ( A O B )

  disjoint A a
  disjoint A b
  disjoint A f
  disjoint a b
  disjoint a f
  disjoint b f
  disjoint A x
  disjoint a x
  disjoint b x
  disjoint A y
  disjoint a y
  disjoint b y
  disjoint B a
  disjoint B b
  disjoint B f
  disjoint B y
  disjoint a ph
  disjoint b ph
  disjoint f ph
  disjoint ph y
  assert |- ( ph -> G : ( ~P B ^m A ) --> ( ~P A ^m B ) )

  proof
    wph
    vf
    cB
    cpw
    cA
    cmap
    co
    #
    vy
    cB
    vy
    cv
    #
    vx
    cv
    vf
    cv
    #
    cfv
    wcel
    #
    vx
    cA
    crab
    #
    cmpt
    #
    cA
    cpw
    #
    cB
    cmap
    co
    #
    cG
    wph
    cG
    cA
    cB
    cO
    co
    vf
    @0
    @5
    cmpt
    fsovfvd.g
    wph
    vx
    vy
    cA
    cB
    vf
    cO
    cV
    cW
    va
    vb
    fsovd.fs
    fsovd.a
    fsovd.b
    fsovd
    syl5eq
    wph
    @5
    @7
    wcel
    #
    @2
    @0
    wcel
    wph
    @8
    cB
    @6
    @5
    wf
    wph
    vy
    cB
    @4
    @6
    @5
    wph
    @4
    @6
    wcel
    @1
    cB
    wcel
    wph
    @4
    cA
    cV
    fsovd.a
    @4
    cA
    wss
    wph
    @3
    vx
    cA
    ssrab2
    a1i
    sselpwd
    adantr
    @5
    eqid
    fmptd
    wph
    @6
    cB
    @5
    cvv
    cW
    wph
    cA
    cV
    wcel
    @6
    cvv
    wcel
    fsovd.a
    cA
    cV
    pwexg
    syl
    fsovd.b
    elmapd
    mpbird
    adantr
    fmpt3d
end
