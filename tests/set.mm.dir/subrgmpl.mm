include "wcel.mm"
include "csubrg.mm"
include "cfv.mm"
include "wa.mm"
include "cmps.mm"
include "co.mm"
include "cbs.mm"
include "wss.mm"
include "cin.mm"
include "simpl.mm"
include "simpr.mm"
include "eqid.mm"
include "ressmplbas2.mm"
include "subrgpsr.mm"
include "crg.mm"
include "subrgrcl.mm"
include "adantl.mm"
include "mplsubrg.mm"
include "subrgin.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "inss2.mm"
include "syl6eqss.mm"
include "wb.mm"
include "mplval2.mm"
include "subsubrg.mm"
include "syl.mm"
include "mpbir2and.mm"

theorem subrgmpl
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cH: class H
  let cI: class I
  let cV: class V
  assume subrgmpl.s: |- S = ( I mPoly R )
  assume subrgmpl.h: |- H = ( R |`s T )
  assume subrgmpl.u: |- U = ( I mPoly H )
  assume subrgmpl.b: |- B = ( Base ` U )


  assert |- ( ( I e. V /\ T e. ( SubRing ` R ) ) -> B e. ( SubRing ` S ) )

  proof
    cI
    cV
    wcel
    #
    cT
    cR
    csubrg
    cfv
    wcel
    #
    wa
    #
    cB
    cS
    csubrg
    cfv
    wcel
    #
    cB
    cI
    cR
    cmps
    co
    #
    csubrg
    cfv
    #
    wcel
    #
    cB
    cS
    cbs
    cfv
    #
    wss
    #
    @2
    cB
    cI
    cH
    cmps
    co
    #
    cbs
    cfv
    #
    @7
    cin
    #
    @5
    @2
    cB
    @10
    cR
    cS
    cT
    cU
    cH
    cI
    @7
    cV
    @9
    subrgmpl.s
    subrgmpl.h
    subrgmpl.u
    subrgmpl.b
    @0
    @1
    simpl
    #
    @0
    @1
    simpr
    @9
    eqid
    #
    @10
    eqid
    #
    @7
    eqid
    #
    ressmplbas2
    #
    @2
    @10
    @5
    wcel
    @7
    @5
    wcel
    #
    @11
    @5
    wcel
    @10
    cR
    @4
    cT
    @9
    cH
    cI
    cV
    @4
    eqid
    #
    subrgmpl.h
    @13
    @14
    subrgpsr
    @2
    cS
    cR
    @4
    @7
    cI
    cV
    @18
    subrgmpl.s
    @15
    @12
    @1
    cR
    crg
    wcel
    @0
    cT
    cR
    subrgrcl
    adantl
    mplsubrg
    #
    @10
    @7
    @4
    subrgin
    syl2anc
    eqeltrd
    @2
    cB
    @11
    @7
    @16
    @10
    @7
    inss2
    syl6eqss
    @2
    @17
    @3
    @6
    @8
    wa
    wb
    @19
    @7
    cB
    @4
    cS
    cS
    cR
    @4
    @7
    cI
    subrgmpl.s
    @18
    @15
    mplval2
    subsubrg
    syl
    mpbir2and
end
