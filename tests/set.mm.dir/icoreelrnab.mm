include "wcel.mm"
include "cv.mm"
include "cico.mm"
include "co.mm"
include "wceq.mm"
include "cr.mm"
include "wrex.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wa.mm"
include "crab.mm"
include "cxp.mm"
include "cres.mm"
include "crn.mm"
include "cima.mm"
include "df-ima.mm"
include "eqtri.mm"
include "eleq2i.mm"
include "cpw.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "icoreresf.mm"
include "ffn.mm"
include "ovelrn.mm"
include "mp2b.mm"
include "bitri.mm"
include "ovres.mm"
include "eqeq2d.mm"
include "2rexbiia.mm"
include "icoreval.mm"

theorem icoreelrnab
  let vz: setvar z
  let cI: class I
  let cX: class X
  let va: setvar a
  let vb: setvar b
  assume icoreelrnab.1: |- I = ( [,) " ( RR X. RR ) )

  disjoint X a
  disjoint X b
  disjoint a b
  disjoint a z
  disjoint b z
  assert |- ( X e. I <-> E. a e. RR E. b e. RR X = { z e. RR | ( a <_ z /\ z < b ) } )

  proof
    cX
    cI
    wcel
    #
    cX
    va
    cv
    #
    vb
    cv
    #
    cico
    co
    #
    wceq
    #
    vb
    cr
    wrex
    va
    cr
    wrex
    #
    cX
    @1
    vz
    cv
    #
    cle
    wbr
    @6
    @2
    clt
    wbr
    wa
    vz
    cr
    crab
    #
    wceq
    #
    vb
    cr
    wrex
    va
    cr
    wrex
    @0
    cX
    @1
    @2
    cico
    cr
    cr
    cxp
    #
    cres
    #
    co
    #
    wceq
    #
    vb
    cr
    wrex
    va
    cr
    wrex
    #
    @5
    @0
    cX
    @10
    crn
    #
    wcel
    #
    @13
    cI
    @14
    cX
    cI
    cico
    @9
    cima
    @14
    icoreelrnab.1
    cico
    @9
    df-ima
    eqtri
    eleq2i
    @9
    cr
    cpw
    #
    @10
    wf
    @10
    @9
    wfn
    @15
    @13
    wb
    icoreresf
    @9
    @16
    @10
    ffn
    va
    vb
    cr
    cr
    cX
    @10
    ovelrn
    mp2b
    bitri
    @12
    @4
    va
    vb
    cr
    cr
    @1
    cr
    wcel
    @2
    cr
    wcel
    wa
    #
    @11
    @3
    cX
    @1
    @2
    cr
    cr
    cico
    ovres
    eqeq2d
    2rexbiia
    bitri
    @4
    @8
    va
    vb
    cr
    cr
    @17
    @3
    @7
    cX
    vz
    @1
    @2
    icoreval
    eqeq2d
    2rexbiia
    bitri
end
