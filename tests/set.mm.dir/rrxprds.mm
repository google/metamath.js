include "wcel.mm"
include "crefld.mm"
include "cfrlm.mm"
include "co.mm"
include "ctch.mm"
include "cfv.mm"
include "cr.mm"
include "csra.mm"
include "csn.mm"
include "cxp.mm"
include "cprds.mm"
include "cress.mm"
include "rrxval.mm"
include "crglmod.mm"
include "cpws.mm"
include "cbs.mm"
include "cfield.mm"
include "wceq.mm"
include "refld.mm"
include "eqid.mm"
include "frlmpws.mm"
include "mpan.mm"
include "cvv.mm"
include "fvex.mm"
include "rlmval.mm"
include "rebase.mm"
include "fveq2i.mm"
include "eqtr4i.mm"
include "oveq1i.mm"
include "csca.mm"
include "ressid.mm"
include "ax-mp.mm"
include "wtru.mm"
include "eqidd.mm"
include "wss.mm"
include "eqimssi.mm"
include "a1i.mm"
include "srasca.mm"
include "trud.mm"
include "eqtr3i.mm"
include "pwsval.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "tchbas.mm"
include "3eqtr4g.mm"
include "oveq12d.mm"
include "eqtr4d.mm"
include "eqtrd.mm"

theorem rrxprds
  let cB: class B
  let cH: class H
  let cI: class I
  let cV: class V
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vx: setvar x
  let vi: setvar i
  assume rrxval.r: |- H = ( RR^ ` I )
  assume rrxbase.b: |- B = ( Base ` H )


  assert |- ( I e. V -> H = ( toCHil ` ( ( RRfld Xs_ ( I X. { ( ( subringAlg ` RRfld ) ` RR ) } ) ) |`s B ) ) )

  proof
    cI
    cV
    wcel
    #
    cH
    crefld
    cI
    cfrlm
    co
    #
    ctch
    cfv
    #
    crefld
    cI
    cr
    crefld
    csra
    cfv
    #
    cfv
    #
    csn
    cxp
    cprds
    co
    #
    cB
    cress
    co
    #
    ctch
    cfv
    cH
    cI
    cV
    rrxval.r
    rrxval
    #
    @0
    @1
    @6
    ctch
    @0
    @1
    crefld
    crglmod
    cfv
    #
    cI
    cpws
    co
    #
    @1
    cbs
    cfv
    #
    cress
    co
    #
    @6
    crefld
    cfield
    wcel
    #
    @0
    @1
    @11
    wceq
    refld
    @10
    crefld
    @1
    cI
    cfield
    cV
    @1
    eqid
    @10
    eqid
    #
    frlmpws
    mpan
    @0
    @5
    @9
    cB
    @10
    cress
    @0
    @9
    @5
    @4
    cvv
    wcel
    @0
    @9
    @5
    wceq
    cr
    @3
    fvex
    @4
    crefld
    cI
    cvv
    cV
    @9
    @8
    @4
    cI
    cpws
    @8
    crefld
    cbs
    cfv
    #
    @3
    cfv
    @4
    crefld
    rlmval
    cr
    @14
    @3
    rebase
    fveq2i
    eqtr4i
    oveq1i
    crefld
    cr
    cress
    co
    #
    crefld
    @4
    csca
    cfv
    #
    @12
    @15
    crefld
    wceq
    refld
    cr
    crefld
    cfield
    rebase
    ressid
    ax-mp
    @15
    @16
    wceq
    wtru
    @4
    cr
    crefld
    wtru
    @4
    eqidd
    cr
    @14
    wss
    wtru
    cr
    @14
    rebase
    eqimssi
    a1i
    srasca
    trud
    eqtr3i
    pwsval
    mpan
    eqcomd
    @0
    cH
    cbs
    cfv
    @2
    cbs
    cfv
    cB
    @10
    @0
    cH
    @2
    cbs
    @7
    fveq2d
    rrxbase.b
    @2
    @10
    @1
    @2
    eqid
    @13
    tchbas
    3eqtr4g
    oveq12d
    eqtr4d
    fveq2d
    eqtrd
end
