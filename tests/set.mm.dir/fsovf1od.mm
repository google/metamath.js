include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "wfn.mm"
include "ccnv.mm"
include "wf1o.mm"
include "fsovfd.mm"
include "ffnd.mm"
include "eqid.mm"
include "fsovcnvd.mm"
include "fneq1d.mm"
include "mpbird.mm"
include "dff1o4.mm"
include "sylanbrc.mm"

theorem fsovf1od
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
  disjoint A x
  disjoint A y
  disjoint a b
  disjoint a f
  disjoint a x
  disjoint a y
  disjoint b f
  disjoint b x
  disjoint b y
  disjoint f x
  disjoint f y
  disjoint x y
  disjoint B a
  disjoint B b
  disjoint B f
  disjoint B x
  disjoint B y
  disjoint a ph
  disjoint b ph
  disjoint f ph
  disjoint ph y
  assert |- ( ph -> G : ( ~P B ^m A ) -1-1-onto-> ( ~P A ^m B ) )

  proof
    wph
    cG
    cB
    cpw
    cA
    cmap
    co
    #
    wfn
    cG
    ccnv
    #
    cA
    cpw
    cB
    cmap
    co
    #
    wfn
    #
    @0
    @2
    cG
    wf1o
    wph
    @0
    @2
    cG
    wph
    vx
    vy
    cA
    cB
    vf
    cG
    cO
    cV
    cW
    va
    vb
    fsovd.fs
    fsovd.a
    fsovd.b
    fsovfvd.g
    fsovfd
    ffnd
    wph
    @3
    cB
    cA
    cO
    co
    #
    @2
    wfn
    wph
    @2
    @0
    @4
    wph
    vx
    vy
    cB
    cA
    vf
    @4
    cO
    cW
    cV
    va
    vb
    fsovd.fs
    fsovd.b
    fsovd.a
    @4
    eqid
    #
    fsovfd
    ffnd
    wph
    @2
    @1
    @4
    wph
    vx
    vy
    cA
    cB
    vf
    cG
    @4
    cO
    cV
    cW
    va
    vb
    fsovd.fs
    fsovd.a
    fsovd.b
    fsovfvd.g
    @5
    fsovcnvd
    fneq1d
    mpbird
    @0
    @2
    cG
    dff1o4
    sylanbrc
end
