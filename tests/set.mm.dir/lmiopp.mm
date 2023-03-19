include "cfv.mm"
include "wbr.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wrex.mm"
include "wceq.mm"
include "lmilmi.mm"
include "eqeq1d.mm"
include "lmicl.mm"
include "lmiinv.mm"
include "wb.mm"
include "eqcom.mm"
include "a1i.mm"
include "3bitr3d.mm"
include "bitrd.mm"
include "mtbird.mm"
include "jca.mm"
include "cmid.mm"
include "cperpg.mm"
include "wo.mm"
include "eqidd.mm"
include "islmib.mm"
include "mpbid.mm"
include "simpld.mm"
include "midbtwn.mm"
include "eleq1.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "islnopp.mm"
include "mpbird.mm"

theorem lmiopp
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let cM: class M
  let c.mi: class .-
  let cO: class O
  let va: setvar a
  let vb: setvar b
  assume lmiopp.p: |- P = ( Base ` G )
  assume lmiopp.m: |- .- = ( dist ` G )
  assume lmiopp.i: |- I = ( Itv ` G )
  assume lmiopp.l: |- L = ( LineG ` G )
  assume lmiopp.g: |- ( ph -> G e. TarskiG )
  assume lmiopp.h: |- ( ph -> G TarskiGDim>= 2 )
  assume lmiopp.d: |- ( ph -> D e. ran L )
  assume lmiopp.o: |- O = { <. a , b >. | ( ( a e. ( P \ D ) /\ b e. ( P \ D ) ) /\ E. t e. D t e. ( a I b ) ) }
  assume lmiopp.n: |- M = ( ( lInvG ` G ) ` D )
  assume lmiopp.a: |- ( ph -> A e. P )
  assume lmiopp.1: |- ( ph -> -. A e. D )

  disjoint .- a
  disjoint .- b
  disjoint .- t
  disjoint a b
  disjoint a t
  disjoint b t
  disjoint A a
  disjoint A b
  disjoint A t
  disjoint D a
  disjoint D b
  disjoint D t
  disjoint G a
  disjoint G b
  disjoint G t
  disjoint I a
  disjoint I b
  disjoint I t
  disjoint M a
  disjoint M b
  disjoint M t
  disjoint O t
  disjoint P a
  disjoint P b
  disjoint P t
  disjoint a ph
  disjoint b ph
  disjoint ph t
  assert |- ( ph -> A O ( M ` A ) )

  proof
    wph
    cA
    cA
    cM
    cfv
    #
    cO
    wbr
    cA
    cD
    wcel
    #
    wn
    #
    @0
    cD
    wcel
    #
    wn
    #
    wa
    #
    vt
    cv
    #
    cA
    @0
    cI
    co
    #
    wcel
    #
    vt
    cD
    wrex
    #
    wa
    wph
    @5
    @9
    wph
    @2
    @4
    lmiopp.1
    wph
    @3
    @1
    lmiopp.1
    wph
    @3
    @0
    cA
    wceq
    #
    @1
    wph
    @0
    cM
    cfv
    #
    @0
    wceq
    cA
    @0
    wceq
    #
    @3
    @10
    wph
    @11
    cA
    @0
    wph
    cA
    cD
    cP
    cG
    cI
    cL
    cM
    c.mi
    lmiopp.p
    lmiopp.m
    lmiopp.i
    lmiopp.g
    lmiopp.h
    lmiopp.n
    lmiopp.l
    lmiopp.d
    lmiopp.a
    lmilmi
    eqeq1d
    wph
    @0
    cD
    cP
    cG
    cI
    cL
    cM
    c.mi
    lmiopp.p
    lmiopp.m
    lmiopp.i
    lmiopp.g
    lmiopp.h
    lmiopp.n
    lmiopp.l
    lmiopp.d
    wph
    cA
    cD
    cP
    cG
    cI
    cL
    cM
    c.mi
    lmiopp.p
    lmiopp.m
    lmiopp.i
    lmiopp.g
    lmiopp.h
    lmiopp.n
    lmiopp.l
    lmiopp.d
    lmiopp.a
    lmicl
    #
    lmiinv
    @12
    @10
    wb
    wph
    cA
    @0
    eqcom
    a1i
    3bitr3d
    wph
    cA
    cD
    cP
    cG
    cI
    cL
    cM
    c.mi
    lmiopp.p
    lmiopp.m
    lmiopp.i
    lmiopp.g
    lmiopp.h
    lmiopp.n
    lmiopp.l
    lmiopp.d
    lmiopp.a
    lmiinv
    bitrd
    mtbird
    jca
    wph
    cA
    @0
    cG
    cmid
    cfv
    co
    #
    cD
    wcel
    #
    @14
    @7
    wcel
    #
    @9
    wph
    @15
    cD
    cA
    @0
    cL
    co
    cG
    cperpg
    cfv
    wbr
    @12
    wo
    #
    wph
    @0
    @0
    wceq
    @15
    @17
    wa
    wph
    @0
    eqidd
    wph
    cA
    @0
    cD
    cP
    cG
    cI
    cL
    cM
    c.mi
    lmiopp.p
    lmiopp.m
    lmiopp.i
    lmiopp.g
    lmiopp.h
    lmiopp.n
    lmiopp.l
    lmiopp.d
    lmiopp.a
    @13
    islmib
    mpbid
    simpld
    wph
    cA
    @0
    cP
    cG
    cI
    c.mi
    lmiopp.p
    lmiopp.m
    lmiopp.i
    lmiopp.g
    lmiopp.h
    lmiopp.a
    @13
    midbtwn
    @8
    @16
    vt
    @14
    cD
    @6
    @14
    @7
    eleq1
    rspcev
    syl2anc
    jca
    wph
    vt
    cA
    @0
    cD
    cP
    cG
    cI
    c.mi
    cO
    va
    vb
    lmiopp.p
    lmiopp.m
    lmiopp.i
    lmiopp.o
    lmiopp.a
    @13
    islnopp
    mpbird
end
