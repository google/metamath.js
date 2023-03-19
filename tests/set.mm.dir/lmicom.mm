include "cfv.mm"
include "wceq.mm"
include "cmid.mm"
include "co.mm"
include "wcel.mm"
include "cperpg.mm"
include "wbr.mm"
include "wo.mm"
include "midcom.mm"
include "wa.mm"
include "eqcomd.mm"
include "islmib.mm"
include "mpbid.mm"
include "simpld.mm"
include "eqeltrrd.mm"
include "wn.mm"
include "wi.mm"
include "simprd.mm"
include "orcomd.mm"
include "ord.mm"
include "cstrkg.mm"
include "adantr.mm"
include "simpr.mm"
include "neqned.mm"
include "tglinecom.mm"
include "breq2d.mm"
include "pm5.74da.mm"
include "orrd.mm"
include "eqcom.mm"
include "orbi2i.mm"
include "sylib.mm"
include "mpbir2and.mm"

theorem lmicom
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let cM: class M
  let c.mi: class .-
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
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
  assume islmib.b: |- ( ph -> B e. P )
  assume lmicom.1: |- ( ph -> ( M ` A ) = B )


  assert |- ( ph -> ( M ` B ) = A )

  proof
    wph
    cA
    cB
    cM
    cfv
    #
    wph
    cA
    @0
    wceq
    cB
    cA
    cG
    cmid
    cfv
    #
    co
    #
    cD
    wcel
    cD
    cB
    cA
    cL
    co
    #
    cG
    cperpg
    cfv
    #
    wbr
    #
    cB
    cA
    wceq
    #
    wo
    #
    wph
    cA
    cB
    @1
    co
    #
    @2
    cD
    wph
    cA
    cB
    cP
    cG
    cI
    c.mi
    ismid.p
    ismid.d
    ismid.i
    ismid.g
    ismid.1
    lmicl.1
    islmib.b
    midcom
    wph
    @8
    cD
    wcel
    #
    cD
    cA
    cB
    cL
    co
    #
    @4
    wbr
    #
    cA
    cB
    wceq
    #
    wo
    #
    wph
    cB
    cA
    cM
    cfv
    #
    wceq
    @9
    @13
    wa
    wph
    @14
    cB
    lmicom.1
    eqcomd
    wph
    cA
    cB
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
    lmicl.1
    islmib.b
    islmib
    mpbid
    #
    simpld
    eqeltrrd
    wph
    @5
    @12
    wo
    @7
    wph
    @12
    @5
    wph
    @12
    @5
    wph
    @12
    wn
    #
    @11
    wi
    @16
    @5
    wi
    wph
    @12
    @11
    wph
    @11
    @12
    wph
    @9
    @13
    @15
    simprd
    orcomd
    ord
    wph
    @16
    @11
    @5
    wph
    @16
    wa
    #
    @10
    @3
    cD
    @4
    @17
    cP
    cA
    cB
    cG
    cI
    cL
    ismid.p
    ismid.i
    lmif.l
    wph
    cG
    cstrkg
    wcel
    @16
    ismid.g
    adantr
    wph
    cA
    cP
    wcel
    @16
    lmicl.1
    adantr
    wph
    cB
    cP
    wcel
    @16
    islmib.b
    adantr
    @17
    cA
    cB
    wph
    @16
    simpr
    neqned
    tglinecom
    breq2d
    pm5.74da
    mpbid
    orrd
    orcomd
    @12
    @6
    @5
    cA
    cB
    eqcom
    orbi2i
    sylib
    wph
    cB
    cA
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
    islmib.b
    lmicl.1
    islmib
    mpbir2and
    eqcomd
end
