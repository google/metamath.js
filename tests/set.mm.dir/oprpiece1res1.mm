include "cicc.mm"
include "co.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cmpt2.mm"
include "cxp.mm"
include "cres.mm"
include "wss.mm"
include "wceq.mm"
include "wcel.mm"
include "cxr.mm"
include "rexri.mm"
include "lbicc2.mm"
include "mp3an.mm"
include "iccss2.mm"
include "mp2an.mm"
include "ssid.mm"
include "resmpt2.mm"
include "reseq1i.mm"
include "w3a.mm"
include "wb.mm"
include "elicc1.mm"
include "simp1bi.mm"
include "ax-mp.mm"
include "iccleub.mm"
include "mp3an12.mm"
include "iftrued.mm"
include "adantr.mm"
include "mpt2eq3ia.mm"
include "eqtr4i.mm"
include "3eqtr4i.mm"

theorem oprpiece1res1
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let cK: class K
  assume oprpiece1.1: |- A e. RR
  assume oprpiece1.2: |- B e. RR
  assume oprpiece1.3: |- A <_ B
  assume oprpiece1.4: |- R e. _V
  assume oprpiece1.5: |- S e. _V
  assume oprpiece1.6: |- K e. ( A [,] B )
  assume oprpiece1.7: |- F = ( x e. ( A [,] B ) , y e. C |-> if ( x <_ K , R , S ) )
  assume oprpiece1.8: |- G = ( x e. ( A [,] K ) , y e. C |-> R )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint K x
  disjoint K y
  assert |- ( F |` ( ( A [,] K ) X. C ) ) = G

  proof
    vx
    vy
    cA
    cB
    cicc
    co
    #
    cC
    vx
    cv
    #
    cK
    cle
    wbr
    #
    cR
    cS
    cif
    #
    cmpt2
    #
    cA
    cK
    cicc
    co
    #
    cC
    cxp
    #
    cres
    #
    vx
    vy
    @5
    cC
    @3
    cmpt2
    #
    cF
    @6
    cres
    cG
    @5
    @0
    wss
    #
    cC
    cC
    wss
    @7
    @8
    wceq
    cA
    @0
    wcel
    #
    cK
    @0
    wcel
    #
    @9
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cA
    cB
    cle
    wbr
    @10
    cA
    oprpiece1.1
    rexri
    #
    cB
    oprpiece1.2
    rexri
    #
    oprpiece1.3
    cA
    cB
    lbicc2
    mp3an
    oprpiece1.6
    cA
    cB
    cA
    cK
    iccss2
    mp2an
    cC
    ssid
    vx
    vy
    @0
    cC
    @5
    cC
    @3
    resmpt2
    mp2an
    cF
    @4
    @6
    oprpiece1.7
    reseq1i
    cG
    vx
    vy
    @5
    cC
    cR
    cmpt2
    @8
    oprpiece1.8
    vx
    vy
    @5
    cC
    @3
    cR
    @1
    @5
    wcel
    #
    @3
    cR
    wceq
    vy
    cv
    cC
    wcel
    @16
    @2
    cR
    cS
    @12
    cK
    cxr
    wcel
    #
    @16
    @2
    @14
    @11
    @17
    oprpiece1.6
    @11
    @17
    cA
    cK
    cle
    wbr
    #
    cK
    cB
    cle
    wbr
    #
    @12
    @13
    @11
    @17
    @18
    @19
    w3a
    wb
    @14
    @15
    cA
    cB
    cK
    elicc1
    mp2an
    simp1bi
    ax-mp
    cA
    cK
    @1
    iccleub
    mp3an12
    iftrued
    adantr
    mpt2eq3ia
    eqtr4i
    3eqtr4i
end
