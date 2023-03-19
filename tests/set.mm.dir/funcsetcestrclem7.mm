include "wcel.mm"
include "wa.mm"
include "ccid.mm"
include "cfv.mm"
include "co.mm"
include "cid.mm"
include "cres.mm"
include "cmap.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "csn.mm"
include "wceq.mm"
include "funcsetcestrclem5.mm"
include "anabsan2.mm"
include "cwun.mm"
include "eqid.mm"
include "adantr.mm"
include "setcbas.mm"
include "syl6reqr.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "setcid.mm"
include "fveq12d.mm"
include "wf.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1of.mm"
include "ax-mp.mm"
include "wb.mm"
include "simpr.mm"
include "elmapg.mm"
include "sylancom.mm"
include "mpbiri.mm"
include "fvresi.mm"
include "syl.mm"
include "1strbas.mm"
include "reseq2d.mm"
include "eqtrd.mm"
include "funcsetcestrclem1.mm"
include "fveq2d.mm"
include "setc1strwun.mm"
include "estrcid.mm"
include "eqtr2d.mm"
include "3eqtrd.mm"

theorem funcsetcestrclem7
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cS: class S
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cX: class X
  let cY: class Y
  assume funcsetcestrc.s: |- S = ( SetCat ` U )
  assume funcsetcestrc.c: |- C = ( Base ` S )
  assume funcsetcestrc.f: |- ( ph -> F = ( x e. C |-> { <. ( Base ` ndx ) , x >. } ) )
  assume funcsetcestrc.u: |- ( ph -> U e. WUni )
  assume funcsetcestrc.o: |- ( ph -> _om e. U )
  assume funcsetcestrc.g: |- ( ph -> G = ( x e. C , y e. C |-> ( _I |` ( y ^m x ) ) ) )
  assume funcsetcestrc.e: |- E = ( ExtStrCat ` U )

  disjoint C x
  disjoint X x
  disjoint ph x
  disjoint C y
  disjoint x y
  disjoint X y
  disjoint ph y
  disjoint Y x
  disjoint Y y
  assert |- ( ( ph /\ X e. C ) -> ( ( X G X ) ` ( ( Id ` S ) ` X ) ) = ( ( Id ` E ) ` ( F ` X ) ) )

  proof
    wph
    cX
    cC
    wcel
    #
    wa
    #
    cX
    cS
    ccid
    cfv
    #
    cfv
    #
    cX
    cX
    cG
    co
    #
    cfv
    cid
    cX
    cres
    #
    cid
    cX
    cX
    cmap
    co
    #
    cres
    #
    cfv
    #
    cid
    cnx
    cbs
    cfv
    cX
    cop
    csn
    #
    cbs
    cfv
    #
    cres
    #
    cX
    cF
    cfv
    #
    cE
    ccid
    cfv
    #
    cfv
    #
    @1
    @3
    @5
    @4
    @7
    wph
    @0
    @4
    @7
    wceq
    wph
    vx
    vy
    cC
    cS
    cU
    cF
    cG
    cX
    cX
    funcsetcestrc.s
    funcsetcestrc.c
    funcsetcestrc.f
    funcsetcestrc.u
    funcsetcestrc.o
    funcsetcestrc.g
    funcsetcestrclem5
    anabsan2
    @1
    cS
    cU
    @2
    cwun
    cX
    funcsetcestrc.s
    @2
    eqid
    wph
    cU
    cwun
    wcel
    @0
    funcsetcestrc.u
    adantr
    #
    wph
    @0
    cX
    cU
    wcel
    wph
    cC
    cU
    cX
    wph
    cU
    cS
    cbs
    cfv
    cC
    wph
    cS
    cU
    cwun
    funcsetcestrc.s
    funcsetcestrc.u
    setcbas
    funcsetcestrc.c
    syl6reqr
    eleq2d
    biimpa
    setcid
    fveq12d
    @1
    @8
    @5
    @11
    @1
    @5
    @6
    wcel
    #
    @8
    @5
    wceq
    @1
    @16
    cX
    cX
    @5
    wf
    #
    cX
    cX
    @5
    wf1o
    @17
    cX
    f1oi
    cX
    cX
    @5
    f1of
    ax-mp
    wph
    @0
    @0
    @16
    @17
    wb
    wph
    @0
    simpr
    #
    cX
    cX
    @5
    cC
    cC
    elmapg
    sylancom
    mpbiri
    @6
    @5
    fvresi
    syl
    @1
    cX
    @10
    cid
    @1
    @0
    cX
    @10
    wceq
    @18
    cX
    @9
    cC
    @9
    eqid
    1strbas
    syl
    reseq2d
    eqtrd
    @1
    @14
    @9
    @13
    cfv
    @11
    @1
    @12
    @9
    @13
    wph
    vx
    cC
    cS
    cU
    cF
    cX
    funcsetcestrc.s
    funcsetcestrc.c
    funcsetcestrc.f
    funcsetcestrclem1
    fveq2d
    @1
    cE
    cU
    @13
    cwun
    @9
    funcsetcestrc.e
    @13
    eqid
    @15
    wph
    cC
    cS
    cU
    cX
    funcsetcestrc.s
    funcsetcestrc.c
    funcsetcestrc.u
    funcsetcestrc.o
    setc1strwun
    estrcid
    eqtr2d
    3eqtrd
end
