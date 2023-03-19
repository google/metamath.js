include "co.mm"
include "wbr.mm"
include "cop.mm"
include "wceq.mm"
include "chom.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "df-br.mm"
include "cbs.mm"
include "eqid.mm"
include "homarcl.mm"
include "homarcl2.mm"
include "simpld.mm"
include "simprd.mm"
include "elhoma.mm"
include "sylbi.mm"
include "ibi.mm"

theorem homa1
  let cC: class C
  let cF: class F
  let cH: class H
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vf: setvar f
  assume homahom.h: |- H = ( HomA ` C )


  assert |- ( Z ( X H Y ) F -> Z = <. X , Y >. )

  proof
    cZ
    cF
    cX
    cY
    cH
    co
    #
    wbr
    #
    cZ
    cX
    cY
    cop
    wceq
    #
    cF
    cX
    cY
    cC
    chom
    cfv
    #
    co
    wcel
    #
    @1
    @2
    @4
    wa
    #
    @1
    cZ
    cF
    cop
    #
    @0
    wcel
    #
    @1
    @5
    wb
    cZ
    cF
    @0
    df-br
    @7
    cC
    cbs
    cfv
    #
    cC
    cF
    cH
    @3
    cX
    cY
    cZ
    homahom.h
    @8
    eqid
    #
    cC
    @6
    cH
    cX
    cY
    homahom.h
    homarcl
    @3
    eqid
    @7
    cX
    @8
    wcel
    #
    cY
    @8
    wcel
    #
    @8
    cC
    @6
    cH
    cX
    cY
    homahom.h
    @9
    homarcl2
    #
    simpld
    @7
    @10
    @11
    @12
    simprd
    elhoma
    sylbi
    ibi
    simpld
end
