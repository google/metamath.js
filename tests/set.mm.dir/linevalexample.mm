include "c5.mm"
include "c3.mm"
include "cfv.mm"
include "co.mm"
include "zring.mm"
include "csg.mm"
include "cmin.mm"
include "c2.mm"
include "ccrg.mm"
include "wcel.mm"
include "wceq.mm"
include "zringcrng.mm"
include "cz.mm"
include "zringbas.mm"
include "eqid.mm"
include "3z.mm"
include "a1i.mm"
include "id.mm"
include "5nn0.mm"
include "nn0zi.mm"
include "lineval.mm"
include "ax-mp.mm"
include "zringsubgval.mm"
include "mp2an.mm"
include "5cn.mm"
include "3cn.mm"
include "2cn.mm"
include "3p2e5.mm"
include "subaddrii.mm"
include "3eqtr2i.mm"

theorem linevalexample
  let cA: class A
  let cB: class B
  let cP: class P
  let cG: class G
  let c.mi: class .-
  let cO: class O
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume linevalexample.p: |- P = ( Poly1 ` ZZring )
  assume linevalexample.b: |- B = ( Base ` P )
  assume linevalexample.x: |- X = ( var1 ` ZZring )
  assume linevalexample.m: |- .- = ( -g ` P )
  assume linevalexample.a: |- A = ( algSc ` P )
  assume linevalexample.g: |- G = ( X .- ( A ` 3 ) )
  assume linevalexample.o: |- O = ( eval1 ` ZZring )


  assert |- ( ( O ` ( X .- ( A ` 3 ) ) ) ` 5 ) = 2

  proof
    c5
    cX
    c3
    cA
    cfv
    c.mi
    co
    #
    cO
    cfv
    cfv
    #
    c5
    c3
    zring
    csg
    cfv
    #
    co
    #
    c5
    c3
    cmin
    co
    #
    c2
    zring
    ccrg
    wcel
    #
    @1
    @3
    wceq
    zringcrng
    @5
    cA
    cB
    c3
    cP
    zring
    @0
    cz
    c.mi
    cO
    c5
    cX
    linevalexample.p
    linevalexample.b
    zringbas
    linevalexample.x
    linevalexample.m
    linevalexample.a
    @0
    eqid
    c3
    cz
    wcel
    #
    @5
    3z
    a1i
    linevalexample.o
    @5
    id
    c5
    cz
    wcel
    #
    @5
    c5
    5nn0
    nn0zi
    #
    a1i
    lineval
    ax-mp
    @7
    @6
    @4
    @3
    wceq
    @8
    3z
    @2
    c5
    c3
    @2
    eqid
    zringsubgval
    mp2an
    c5
    c3
    c2
    5cn
    3cn
    2cn
    3p2e5
    subaddrii
    3eqtr2i
end
