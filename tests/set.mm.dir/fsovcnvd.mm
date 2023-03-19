include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "fsovfd.mm"
include "fsovcnvlem.mm"
include "2fcoidinvd.mm"

theorem fsovcnvd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cG: class G
  let cH: class H
  let cO: class O
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  assume fsovd.fs: |- O = ( a e. _V , b e. _V |-> ( f e. ( ~P b ^m a ) |-> ( y e. b |-> { x e. a | y e. ( f ` x ) } ) ) )
  assume fsovd.a: |- ( ph -> A e. V )
  assume fsovd.b: |- ( ph -> B e. W )
  assume fsovfvd.g: |- G = ( A O B )
  assume fsovcnvlem.h: |- H = ( B O A )

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
  assert |- ( ph -> `' G = H )

  proof
    wph
    cB
    cpw
    cA
    cmap
    co
    cA
    cpw
    cB
    cmap
    co
    cG
    cH
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
    wph
    vx
    vy
    cB
    cA
    vf
    cH
    cO
    cW
    cV
    va
    vb
    fsovd.fs
    fsovd.b
    fsovd.a
    fsovcnvlem.h
    fsovfd
    wph
    vx
    vy
    cA
    cB
    vf
    cG
    cH
    cO
    cV
    cW
    va
    vb
    fsovd.fs
    fsovd.a
    fsovd.b
    fsovfvd.g
    fsovcnvlem.h
    fsovcnvlem
    wph
    vx
    vy
    cB
    cA
    vf
    cH
    cG
    cO
    cW
    cV
    va
    vb
    fsovd.fs
    fsovd.b
    fsovd.a
    fsovcnvlem.h
    fsovfvd.g
    fsovcnvlem
    2fcoidinvd
end
