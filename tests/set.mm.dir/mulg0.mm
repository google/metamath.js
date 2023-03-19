include "cc0.mm"
include "cz.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "0z.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cplusg.mm"
include "cfv.mm"
include "cn.mm"
include "csn.mm"
include "cxp.mm"
include "c1.mm"
include "cseq.mm"
include "cneg.mm"
include "cminusg.mm"
include "cif.mm"
include "eqid.mm"
include "mulgval.mm"
include "iftruei.mm"
include "syl6eq.mm"
include "mpan.mm"

theorem mulg0
  let cB: class B
  let c.x: class .x.
  let cG: class G
  let cX: class X
  let c.0: class .0.
  assume mulg0.b: |- B = ( Base ` G )
  assume mulg0.o: |- .0. = ( 0g ` G )
  assume mulg0.t: |- .x. = ( .g ` G )


  assert |- ( X e. B -> ( 0 .x. X ) = .0. )

  proof
    cc0
    cz
    wcel
    #
    cX
    cB
    wcel
    #
    cc0
    cX
    c.x
    co
    #
    c.0
    wceq
    0z
    @0
    @1
    wa
    @2
    cc0
    cc0
    wceq
    #
    c.0
    cc0
    cc0
    clt
    wbr
    cc0
    cG
    cplusg
    cfv
    #
    cn
    cX
    csn
    cxp
    c1
    cseq
    #
    cfv
    cc0
    cneg
    @5
    cfv
    cG
    cminusg
    cfv
    #
    cfv
    cif
    #
    cif
    c.0
    cB
    @4
    @5
    c.x
    cG
    @6
    cc0
    cX
    c.0
    mulg0.b
    @4
    eqid
    mulg0.o
    @6
    eqid
    mulg0.t
    @5
    eqid
    mulgval
    @3
    c.0
    @7
    cc0
    eqid
    iftruei
    syl6eq
    mpan
end
