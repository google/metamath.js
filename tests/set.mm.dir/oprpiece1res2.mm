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
include "ubicc2.mm"
include "mp3an.mm"
include "iccss2.mm"
include "mp2an.mm"
include "ssid.mm"
include "resmpt2.mm"
include "reseq1i.mm"
include "wa.mm"
include "ad2antlr.mm"
include "simpr.mm"
include "cr.mm"
include "elicc2i.mm"
include "simp1bi.mm"
include "ax-mp.mm"
include "simp2bi.mm"
include "ad2antrr.mm"
include "wb.mm"
include "letri3.mm"
include "sylancl.mm"
include "mpbir2and.mm"
include "syl.mm"
include "3eqtr4d.mm"
include "wn.mm"
include "eqidd.mm"
include "ifeqda.mm"
include "mpt2eq3ia.mm"
include "eqtr4i.mm"
include "3eqtr4i.mm"

theorem oprpiece1res2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
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
  assume oprpiece1.9: |- ( x = K -> R = P )
  assume oprpiece1.10: |- ( x = K -> S = Q )
  assume oprpiece1.11: |- ( y e. C -> P = Q )
  assume oprpiece1.12: |- G = ( x e. ( K [,] B ) , y e. C |-> S )

  disjoint P x
  disjoint Q x
  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint K x
  disjoint K y
  assert |- ( F |` ( ( K [,] B ) X. C ) ) = G

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
    cK
    cB
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
    cK
    @0
    wcel
    #
    cB
    @0
    wcel
    #
    @9
    oprpiece1.6
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    cA
    cB
    cle
    wbr
    @11
    cA
    oprpiece1.1
    rexri
    cB
    oprpiece1.2
    rexri
    oprpiece1.3
    cA
    cB
    ubicc2
    mp3an
    cA
    cB
    cK
    cB
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
    cS
    cmpt2
    @8
    oprpiece1.12
    vx
    vy
    @5
    cC
    @3
    cS
    @1
    @5
    wcel
    #
    vy
    cv
    cC
    wcel
    #
    wa
    #
    @2
    cR
    cS
    cS
    @14
    @2
    wa
    #
    cP
    cQ
    cR
    cS
    @13
    cP
    cQ
    wceq
    @12
    @2
    oprpiece1.11
    ad2antlr
    @15
    @1
    cK
    wceq
    #
    cR
    cP
    wceq
    @15
    @16
    @2
    cK
    @1
    cle
    wbr
    #
    @14
    @2
    simpr
    @12
    @17
    @13
    @2
    @12
    @1
    cr
    wcel
    #
    @17
    @1
    cB
    cle
    wbr
    #
    cK
    cB
    @1
    @10
    cK
    cr
    wcel
    #
    oprpiece1.6
    @10
    @20
    cA
    cK
    cle
    wbr
    cK
    cB
    cle
    wbr
    cA
    cB
    cK
    oprpiece1.1
    oprpiece1.2
    elicc2i
    simp1bi
    ax-mp
    #
    oprpiece1.2
    elicc2i
    #
    simp2bi
    ad2antrr
    @15
    @18
    @20
    @16
    @2
    @17
    wa
    wb
    @12
    @18
    @13
    @2
    @12
    @18
    @17
    @19
    @22
    simp1bi
    ad2antrr
    @21
    @1
    cK
    letri3
    sylancl
    mpbir2and
    #
    oprpiece1.9
    syl
    @15
    @16
    cS
    cQ
    wceq
    @23
    oprpiece1.10
    syl
    3eqtr4d
    @14
    @2
    wn
    wa
    cS
    eqidd
    ifeqda
    mpt2eq3ia
    eqtr4i
    3eqtr4i
end
