include "cfn.mm"
include "wcel.mm"
include "ccnfld.mm"
include "csca.mm"
include "cfv.mm"
include "cr.mm"
include "cress.mm"
include "co.mm"
include "csn.mm"
include "cxp.mm"
include "cprds.mm"
include "cds.mm"
include "cbs.mm"
include "cme.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cres.mm"
include "cvv.mm"
include "cmpt.mm"
include "fconstmpt.mm"
include "oveq2i.mm"
include "eqid.mm"
include "cc.mm"
include "wss.mm"
include "wceq.mm"
include "ax-resscn.mm"
include "cnfldbas.mm"
include "ressbas2.mm"
include "ax-mp.mm"
include "reex.mm"
include "cnfldds.mm"
include "ressds.mm"
include "reseq1i.mm"
include "fvexd.mm"
include "id.mm"
include "cv.mm"
include "wa.mm"
include "ovex.mm"
include "a1i.mm"
include "remet.mm"
include "prdsmet.mm"
include "resssca.mm"
include "pwsval.mm"
include "mpan.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "cmap.mm"
include "pwsbas.mm"
include "eqtrd.mm"
include "3eltr4d.mm"

theorem repwsmet
  let cD: class D
  let cI: class I
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vr: setvar r
  let vz: setvar z
  let cF: class F
  let cG: class G
  let wph: wff ph
  assume rrnequiv.y: |- Y = ( ( CCfld |`s RR ) ^s I )
  assume rrnequiv.d: |- D = ( dist ` Y )
  assume rrnequiv.1: |- X = ( RR ^m I )


  assert |- ( I e. Fin -> D e. ( Met ` X ) )

  proof
    cI
    cfn
    wcel
    #
    ccnfld
    csca
    cfv
    #
    cI
    ccnfld
    cr
    cress
    co
    #
    csn
    cxp
    #
    cprds
    co
    #
    cds
    cfv
    #
    @4
    cbs
    cfv
    #
    cme
    cfv
    cD
    cX
    cme
    cfv
    @0
    vk
    @6
    @5
    @2
    @1
    cabs
    cmin
    ccom
    #
    cr
    cr
    cxp
    #
    cres
    #
    cI
    cr
    cvv
    @4
    cvv
    @3
    vk
    cI
    @2
    cmpt
    @1
    cprds
    vk
    cI
    @2
    fconstmpt
    oveq2i
    @6
    eqid
    cr
    cc
    wss
    cr
    @2
    cbs
    cfv
    wceq
    ax-resscn
    cr
    cc
    @2
    ccnfld
    @2
    eqid
    #
    cnfldbas
    ressbas2
    ax-mp
    #
    @7
    @2
    cds
    cfv
    #
    @8
    cr
    cvv
    wcel
    #
    @7
    @12
    wceq
    reex
    cr
    @7
    ccnfld
    @2
    cvv
    @10
    cnfldds
    ressds
    ax-mp
    reseq1i
    @5
    eqid
    @0
    ccnfld
    csca
    fvexd
    @0
    id
    @2
    cvv
    wcel
    #
    @0
    vk
    cv
    cI
    wcel
    wa
    #
    ccnfld
    cr
    cress
    ovex
    #
    a1i
    @9
    cr
    cme
    cfv
    wcel
    @15
    @9
    @9
    eqid
    remet
    a1i
    prdsmet
    @0
    cD
    cY
    cds
    cfv
    @5
    rrnequiv.d
    @0
    cY
    @4
    cds
    @14
    @0
    cY
    @4
    wceq
    @16
    @2
    @1
    cI
    cvv
    cfn
    cY
    rrnequiv.y
    @13
    @1
    @2
    csca
    cfv
    wceq
    reex
    cr
    @1
    ccnfld
    @2
    cvv
    @10
    @1
    eqid
    resssca
    ax-mp
    pwsval
    mpan
    #
    fveq2d
    syl5eq
    @0
    cX
    @6
    cme
    @0
    cX
    cr
    cI
    cmap
    co
    #
    @6
    rrnequiv.1
    @0
    @18
    cY
    cbs
    cfv
    #
    @6
    @14
    @0
    @18
    @19
    wceq
    @16
    cr
    @2
    cI
    cvv
    cfn
    cY
    rrnequiv.y
    @11
    pwsbas
    mpan
    @0
    cY
    @4
    cbs
    @17
    fveq2d
    eqtrd
    syl5eq
    fveq2d
    3eltr4d
end
