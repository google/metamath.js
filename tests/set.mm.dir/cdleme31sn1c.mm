include "wcel.mm"
include "co.mm"
include "wbr.mm"
include "wa.mm"
include "csb.mm"
include "cv.mm"
include "wn.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "eqid.mm"
include "cdleme31sn1.mm"
include "cdleme31se.mm"
include "adantr.mm"
include "eqeq2d.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "riotabidv.mm"
include "syl6eqr.mm"
include "eqtrd.mm"

theorem cdleme31sn1c
  let vy: setvar y
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cE: class E
  let cG: class G
  let cI: class I
  let c.or: class .\/
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cW: class W
  let cY: class Y
  let vs: setvar s
  assume cdleme31sn1c.g: |- G = ( ( P .\/ Q ) ./\ ( E .\/ ( ( s .\/ t ) ./\ W ) ) )
  assume cdleme31sn1c.i: |- I = ( iota_ y e. B A. t e. A ( ( -. t .<_ W /\ -. t .<_ ( P .\/ Q ) ) -> y = G ) )
  assume cdleme31sn1c.n: |- N = if ( s .<_ ( P .\/ Q ) , I , D )
  assume cdleme31sn1c.y: |- Y = ( ( P .\/ Q ) ./\ ( E .\/ ( ( R .\/ t ) ./\ W ) ) )
  assume cdleme31sn1c.c: |- C = ( iota_ y e. B A. t e. A ( ( -. t .<_ W /\ -. t .<_ ( P .\/ Q ) ) -> y = Y ) )

  disjoint s t
  disjoint s y
  disjoint A s
  disjoint t y
  disjoint A t
  disjoint A y
  disjoint B s
  disjoint E s
  disjoint .\/ s
  disjoint .\/ t
  disjoint .\/ y
  disjoint .<_ s
  disjoint .<_ t
  disjoint .<_ y
  disjoint ./\ s
  disjoint P s
  disjoint P t
  disjoint P y
  disjoint Q s
  disjoint Q t
  disjoint Q y
  disjoint R s
  disjoint R t
  disjoint R y
  disjoint W s
  assert |- ( ( R e. A /\ R .<_ ( P .\/ Q ) ) -> [_ R / s ]_ N = C )

  proof
    cR
    cA
    wcel
    #
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    wa
    #
    vs
    cR
    cN
    csb
    vt
    cv
    #
    cW
    c.le
    wbr
    wn
    @4
    @1
    c.le
    wbr
    wn
    wa
    #
    vy
    cv
    #
    vs
    cR
    cG
    csb
    #
    wceq
    #
    wi
    #
    vt
    cA
    wral
    #
    vy
    cB
    crio
    #
    cC
    vy
    vt
    cA
    cB
    @11
    cD
    cP
    cQ
    cR
    cG
    cI
    c.or
    c.le
    cN
    cW
    vs
    cdleme31sn1c.i
    cdleme31sn1c.n
    @11
    eqid
    cdleme31sn1
    @3
    @11
    @5
    @6
    cY
    wceq
    #
    wi
    #
    vt
    cA
    wral
    #
    vy
    cB
    crio
    cC
    @3
    @10
    @14
    vy
    cB
    @3
    @9
    @13
    vt
    cA
    @3
    @8
    @12
    @5
    @3
    @7
    cY
    @6
    @0
    @7
    cY
    wceq
    @2
    cA
    cE
    cP
    cQ
    cR
    @4
    cG
    c.or
    c.an
    cW
    cY
    vs
    cdleme31sn1c.g
    cdleme31sn1c.y
    cdleme31se
    adantr
    eqeq2d
    imbi2d
    ralbidv
    riotabidv
    cdleme31sn1c.c
    syl6eqr
    eqtrd
end
