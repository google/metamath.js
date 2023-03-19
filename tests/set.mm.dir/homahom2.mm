include "co.mm"
include "wbr.mm"
include "cop.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "df-br.mm"
include "cbs.mm"
include "cfv.mm"
include "eqid.mm"
include "homarcl.mm"
include "homarcl2.mm"
include "simpld.mm"
include "simprd.mm"
include "elhoma.mm"
include "sylbi.mm"
include "ibi.mm"

theorem homahom2
  let cC: class C
  let cF: class F
  let cH: class H
  let cJ: class J
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vf: setvar f
  assume homahom.h: |- H = ( HomA ` C )
  assume homahom.j: |- J = ( Hom ` C )


  assert |- ( Z ( X H Y ) F -> F e. ( X J Y ) )

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
    cJ
    co
    wcel
    #
    @1
    @2
    @3
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
    @4
    wb
    cZ
    cF
    @0
    df-br
    @6
    cC
    cbs
    cfv
    #
    cC
    cF
    cH
    cJ
    cX
    cY
    cZ
    homahom.h
    @7
    eqid
    #
    cC
    @5
    cH
    cX
    cY
    homahom.h
    homarcl
    homahom.j
    @6
    cX
    @7
    wcel
    #
    cY
    @7
    wcel
    #
    @7
    cC
    @5
    cH
    cX
    cY
    homahom.h
    @8
    homarcl2
    #
    simpld
    @6
    @9
    @10
    @11
    simprd
    elhoma
    sylbi
    ibi
    simprd
end
