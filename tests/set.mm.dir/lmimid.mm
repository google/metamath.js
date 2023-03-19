include "cfv.mm"
include "wceq.mm"
include "cmid.mm"
include "co.mm"
include "wcel.mm"
include "cperpg.mm"
include "wbr.mm"
include "wo.mm"
include "cmir.mm"
include "a1i.mm"
include "fveq1d.mm"
include "eqid.mm"
include "tglnpt.mm"
include "mircl.mm"
include "ismidb.mm"
include "mpbid.mm"
include "eqeltrd.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "wa.mm"
include "cstrkg.mm"
include "adantr.mm"
include "crn.mm"
include "simpr.mm"
include "tgelrnln.mm"
include "midbtwn.mm"
include "eqeltrrd.mm"
include "btwnlng1.mm"
include "elind.mm"
include "tglinerflx1.mm"
include "mirinv.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "biimpar.mm"
include "eqcomd.mm"
include "ex.mm"
include "necon3d.mm"
include "imp.mm"
include "cs3.mm"
include "crag.mm"
include "ragperp.mm"
include "syl5bir.mm"
include "orrd.mm"
include "orcomd.mm"
include "islmib.mm"
include "mpbir2and.mm"

theorem lmimid
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cS: class S
  let cG: class G
  let cI: class I
  let cL: class L
  let cM: class M
  let c.mi: class .-
  let vb: setvar b
  let vm: setvar m
  let va: setvar a
  let vg: setvar g
  let vd: setvar d
  assume ismid.p: |- P = ( Base ` G )
  assume ismid.d: |- .- = ( dist ` G )
  assume ismid.i: |- I = ( Itv ` G )
  assume ismid.g: |- ( ph -> G e. TarskiG )
  assume ismid.1: |- ( ph -> G TarskiGDim>= 2 )
  assume lmif.m: |- M = ( ( lInvG ` G ) ` D )
  assume lmif.l: |- L = ( LineG ` G )
  assume lmif.d: |- ( ph -> D e. ran L )
  assume lmicl.1: |- ( ph -> A e. P )
  assume lmimid.s: |- S = ( ( pInvG ` G ) ` B )
  assume lmimid.r: |- ( ph -> <" A B C "> e. ( raG ` G ) )
  assume lmimid.a: |- ( ph -> A e. D )
  assume lmimid.b: |- ( ph -> B e. D )
  assume lmimid.c: |- ( ph -> C e. P )
  assume lmimid.d: |- ( ph -> A =/= B )


  assert |- ( ph -> ( M ` C ) = ( S ` C ) )

  proof
    wph
    cC
    cS
    cfv
    #
    cC
    cM
    cfv
    #
    wph
    @0
    @1
    wceq
    cC
    @0
    cG
    cmid
    cfv
    co
    #
    cD
    wcel
    cD
    cC
    @0
    cL
    co
    #
    cG
    cperpg
    cfv
    wbr
    #
    cC
    @0
    wceq
    #
    wo
    wph
    @2
    cB
    cD
    wph
    @0
    cC
    cB
    cG
    cmir
    cfv
    #
    cfv
    #
    cfv
    wceq
    @2
    cB
    wceq
    wph
    cC
    cS
    @7
    cS
    @7
    wceq
    wph
    lmimid.s
    a1i
    fveq1d
    wph
    cC
    @0
    cP
    @6
    cG
    cI
    cB
    c.mi
    ismid.p
    ismid.d
    ismid.i
    ismid.g
    ismid.1
    lmimid.c
    wph
    cB
    cP
    @6
    cG
    cI
    cL
    cS
    c.mi
    cC
    ismid.p
    ismid.d
    ismid.i
    lmif.l
    @6
    eqid
    #
    ismid.g
    wph
    cD
    cP
    cG
    cI
    cL
    cB
    ismid.p
    lmif.l
    ismid.i
    ismid.g
    lmif.d
    lmimid.b
    tglnpt
    #
    lmimid.s
    lmimid.c
    mircl
    #
    @8
    @9
    ismidb
    mpbid
    #
    lmimid.b
    eqeltrd
    wph
    @5
    @4
    wph
    @5
    @4
    @5
    wn
    cC
    @0
    wne
    #
    wph
    @4
    cC
    @0
    df-ne
    wph
    @12
    @4
    wph
    @12
    wa
    #
    cD
    @3
    cP
    cA
    cG
    cI
    cL
    c.mi
    cC
    cB
    ismid.p
    ismid.d
    ismid.i
    lmif.l
    wph
    cG
    cstrkg
    wcel
    @12
    ismid.g
    adantr
    #
    wph
    cD
    cL
    crn
    wcel
    @12
    lmif.d
    adantr
    @13
    cP
    cG
    cI
    cL
    cC
    @0
    ismid.p
    ismid.i
    lmif.l
    @14
    wph
    cC
    cP
    wcel
    @12
    lmimid.c
    adantr
    #
    wph
    @0
    cP
    wcel
    @12
    @10
    adantr
    #
    wph
    @12
    simpr
    #
    tgelrnln
    @13
    cD
    @3
    cB
    wph
    cB
    cD
    wcel
    @12
    lmimid.b
    adantr
    @13
    cP
    cG
    cI
    cL
    cC
    @0
    cB
    ismid.p
    ismid.i
    lmif.l
    @14
    @15
    @16
    wph
    cB
    cP
    wcel
    @12
    @9
    adantr
    @17
    wph
    cB
    cC
    @0
    cI
    co
    #
    wcel
    @12
    wph
    @2
    cB
    @18
    @11
    wph
    cC
    @0
    cP
    cG
    cI
    c.mi
    ismid.p
    ismid.d
    ismid.i
    ismid.g
    ismid.1
    lmimid.c
    @10
    midbtwn
    eqeltrrd
    adantr
    btwnlng1
    elind
    wph
    cA
    cD
    wcel
    @12
    lmimid.a
    adantr
    @13
    cP
    cC
    @0
    cG
    cI
    cL
    ismid.p
    ismid.i
    lmif.l
    @14
    @15
    @16
    @17
    tglinerflx1
    wph
    cA
    cB
    wne
    @12
    lmimid.d
    adantr
    wph
    @12
    cC
    cB
    wne
    wph
    cC
    cB
    cC
    @0
    wph
    cC
    cB
    wceq
    #
    @5
    wph
    @19
    wa
    @0
    cC
    wph
    @0
    cC
    wceq
    #
    @19
    wph
    @20
    cB
    cC
    wceq
    @19
    wph
    cB
    cC
    cP
    @6
    cG
    cI
    cL
    cS
    c.mi
    ismid.p
    ismid.d
    ismid.i
    lmif.l
    @8
    ismid.g
    @9
    lmimid.s
    lmimid.c
    mirinv
    cB
    cC
    eqcom
    syl6bb
    biimpar
    eqcomd
    ex
    necon3d
    imp
    wph
    cA
    cB
    cC
    cs3
    cG
    crag
    cfv
    wcel
    @12
    lmimid.r
    adantr
    ragperp
    ex
    syl5bir
    orrd
    orcomd
    wph
    cC
    @0
    cD
    cP
    cG
    cI
    cL
    cM
    c.mi
    ismid.p
    ismid.d
    ismid.i
    ismid.g
    ismid.1
    lmif.m
    lmif.l
    lmif.d
    lmimid.c
    @10
    islmib
    mpbir2and
    eqcomd
end
