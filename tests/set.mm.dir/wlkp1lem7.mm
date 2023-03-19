include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cpr.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "ciedg.mm"
include "cv.mm"
include "wceq.mm"
include "cc0.mm"
include "cfz.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "wlkp1lem5.mm"
include "cwlks.mm"
include "wbr.mm"
include "chash.mm"
include "cn0.mm"
include "wcel.mm"
include "wlkcl.mm"
include "eqcomi.mm"
include "eleq1i.mm"
include "nn0fz0.mm"
include "sylbb.mm"
include "3syl.mm"
include "rspcdva.mm"
include "fveq1i.mm"
include "cvv.mm"
include "cdm.mm"
include "wn.mm"
include "ovex.mm"
include "wlkp1lem1.mm"
include "fsnunfv.mm"
include "mp3an2i.mm"
include "syl5eq.mm"
include "preq12d.mm"
include "cedg.mm"
include "syl3anc.mm"
include "3sstr4d.mm"
include "wlkp1lem3.mm"
include "sseqtr4d.mm"

theorem wlkp1lem7
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cN: class N
  let cV: class V
  let vk: setvar k
  let vx: setvar x
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


  assert |- ( ph -> { ( Q ` N ) , ( Q ` ( N + 1 ) ) } C_ ( ( iEdg ` S ) ` ( H ` N ) ) )

  proof
    wph
    cN
    cQ
    cfv
    #
    cN
    c1
    caddc
    co
    #
    cQ
    cfv
    #
    cpr
    #
    cB
    cI
    cB
    cE
    cop
    csn
    cun
    cfv
    #
    cN
    cH
    cfv
    cS
    ciedg
    cfv
    cfv
    wph
    cN
    cP
    cfv
    #
    cC
    cpr
    cE
    @3
    @4
    wlkp1.x
    wph
    @0
    @5
    @2
    cC
    wph
    vk
    cv
    #
    cQ
    cfv
    #
    @6
    cP
    cfv
    #
    wceq
    @0
    @5
    wceq
    vk
    cc0
    cN
    cfz
    co
    #
    cN
    @6
    cN
    wceq
    @7
    @0
    @8
    @5
    @6
    cN
    cQ
    fveq2
    @6
    cN
    cP
    fveq2
    eqeq12d
    wph
    cB
    cC
    cP
    cQ
    cS
    vk
    cE
    cF
    cG
    cH
    cI
    cN
    cV
    wlkp1.v
    wlkp1.i
    wlkp1.f
    wlkp1.a
    wlkp1.b
    wlkp1.c
    wlkp1.d
    wlkp1.w
    wlkp1.n
    wlkp1.e
    wlkp1.x
    wlkp1.u
    wlkp1.h
    wlkp1.q
    wlkp1.s
    wlkp1lem5
    wph
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    cF
    chash
    cfv
    #
    cn0
    wcel
    #
    cN
    @9
    wcel
    #
    wlkp1.w
    cP
    cF
    cG
    wlkcl
    @11
    cN
    cn0
    wcel
    @12
    @10
    cN
    cn0
    cN
    @10
    wlkp1.n
    eqcomi
    eleq1i
    cN
    nn0fz0
    sylbb
    3syl
    rspcdva
    wph
    @2
    @1
    cP
    @1
    cC
    cop
    csn
    cun
    #
    cfv
    #
    cC
    @1
    cQ
    @13
    wlkp1.q
    fveq1i
    @1
    cvv
    wcel
    wph
    cC
    cV
    wcel
    @1
    cP
    cdm
    wcel
    wn
    @14
    cC
    wceq
    cN
    c1
    caddc
    ovex
    wlkp1.c
    wph
    cB
    cC
    cP
    cF
    cG
    cI
    cN
    cV
    wlkp1.v
    wlkp1.i
    wlkp1.f
    wlkp1.a
    wlkp1.b
    wlkp1.c
    wlkp1.d
    wlkp1.w
    wlkp1.n
    wlkp1lem1
    cP
    cvv
    cV
    @1
    cC
    fsnunfv
    mp3an2i
    syl5eq
    preq12d
    wph
    cB
    cvv
    wcel
    cE
    cG
    cedg
    cfv
    #
    wcel
    cB
    cI
    cdm
    wcel
    wn
    @4
    cE
    wceq
    wlkp1.b
    wlkp1.e
    wlkp1.d
    cI
    cvv
    @15
    cB
    cE
    fsnunfv
    syl3anc
    3sstr4d
    wph
    cB
    cC
    cP
    cS
    cE
    cF
    cG
    cH
    cI
    cN
    cV
    wlkp1.v
    wlkp1.i
    wlkp1.f
    wlkp1.a
    wlkp1.b
    wlkp1.c
    wlkp1.d
    wlkp1.w
    wlkp1.n
    wlkp1.e
    wlkp1.x
    wlkp1.u
    wlkp1.h
    wlkp1lem3
    sseqtr4d
end
