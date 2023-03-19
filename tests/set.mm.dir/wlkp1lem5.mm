include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "fveq1i.mm"
include "wne.mm"
include "wn.mm"
include "wi.mm"
include "fzp1nel.mm"
include "wb.mm"
include "eleq1.mm"
include "notbid.mm"
include "eqcoms.mm"
include "mpbiri.mm"
include "a1i.mm"
include "con2d.mm"
include "imp.mm"
include "neqned.mm"
include "fvunsn.mm"
include "syl.mm"
include "syl5eq.mm"
include "ralrimiva.mm"

theorem wlkp1lem5
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cS: class S
  let vk: setvar k
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cN: class N
  let cV: class V
  assume wlkp1.v: |- V = ( Vtx ` G )
  assume wlkp1.i: |- I = ( iEdg ` G )
  assume wlkp1.f: |- ( ph -> Fun I )
  assume wlkp1.a: |- ( ph -> I e. Fin )
  assume wlkp1.b: |- ( ph -> B e. _V )
  assume wlkp1.c: |- ( ph -> C e. V )
  assume wlkp1.d: |- ( ph -> -. B e. dom I )
  assume wlkp1.w: |- ( ph -> F ( Walks ` G ) P )
  assume wlkp1.n: |- N = ( # ` F )
  assume wlkp1.e: |- ( ph -> E e. ( Edg ` G ) )
  assume wlkp1.x: |- ( ph -> { ( P ` N ) , C } C_ E )
  assume wlkp1.u: |- ( ph -> ( iEdg ` S ) = ( I u. { <. B , E >. } ) )
  assume wlkp1.h: |- H = ( F u. { <. N , B >. } )
  assume wlkp1.q: |- Q = ( P u. { <. ( N + 1 ) , C >. } )
  assume wlkp1.s: |- ( ph -> ( Vtx ` S ) = V )

  disjoint k ph
  assert |- ( ph -> A. k e. ( 0 ... N ) ( Q ` k ) = ( P ` k ) )

  proof
    wph
    vk
    cv
    #
    cQ
    cfv
    #
    @0
    cP
    cfv
    #
    wceq
    vk
    cc0
    cN
    cfz
    co
    #
    wph
    @0
    @3
    wcel
    #
    wa
    #
    @1
    @0
    cP
    cN
    c1
    caddc
    co
    #
    cC
    cop
    csn
    cun
    #
    cfv
    #
    @2
    @0
    cQ
    @7
    wlkp1.q
    fveq1i
    @5
    @6
    @0
    wne
    @8
    @2
    wceq
    @5
    @6
    @0
    wph
    @4
    @6
    @0
    wceq
    #
    wn
    wph
    @9
    @4
    @9
    @4
    wn
    #
    wi
    wph
    @9
    @10
    @6
    @3
    wcel
    #
    wn
    #
    cc0
    cN
    fzp1nel
    @10
    @12
    wb
    @0
    @6
    @0
    @6
    wceq
    @4
    @11
    @0
    @6
    @3
    eleq1
    notbid
    eqcoms
    mpbiri
    a1i
    con2d
    imp
    neqned
    cP
    @6
    cC
    @0
    fvunsn
    syl
    syl5eq
    ralrimiva
end
