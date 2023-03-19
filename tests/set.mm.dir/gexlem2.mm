include "wcel.mm"
include "cn.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "c1.mm"
include "cfz.mm"
include "wa.mm"
include "crab.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "ralbidv.mm"
include "elrab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "c0.mm"
include "cc0.mm"
include "cif.mm"
include "eqid.mm"
include "gexval.mm"
include "wne.mm"
include "ne0i.mm"
include "ifnefalse.mm"
include "syl.mm"
include "sylan9eq.mm"
include "cle.mm"
include "wbr.mm"
include "ssrab2.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "nnuz.mm"
include "sseqtri.mm"
include "adantl.mm"
include "infssuzcl.mm"
include "sylancr.mm"
include "sseldi.mm"
include "infssuzle.mm"
include "mpan.mm"
include "wb.mm"
include "cz.mm"
include "elrabi.mm"
include "nnzd.mm"
include "fznn.mm"
include "mpbir2and.mm"
include "eqeltrd.mm"
include "sylan2br.mm"
include "3impb.mm"

theorem gexlem2
  let vx: setvar x
  let c.x: class .x.
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let cX: class X
  let c.0: class .0.
  let cA: class A
  let vy: setvar y
  assume gexcl.1: |- X = ( Base ` G )
  assume gexcl.2: |- E = ( gEx ` G )
  assume gexid.3: |- .x. = ( .g ` G )
  assume gexid.4: |- .0. = ( 0g ` G )

  disjoint E x
  disjoint G x
  disjoint N x
  disjoint V x
  disjoint X x
  disjoint .0. x
  disjoint .x. x
  disjoint A x
  disjoint x y
  disjoint E y
  disjoint G y
  disjoint N y
  disjoint V y
  disjoint X y
  disjoint .0. y
  disjoint .x. y
  assert |- ( ( G e. V /\ N e. NN /\ A. x e. X ( N .x. x ) = .0. ) -> E e. ( 1 ... N ) )

  proof
    cG
    cV
    wcel
    #
    cN
    cn
    wcel
    #
    cN
    vx
    cv
    #
    c.x
    co
    #
    c.0
    wceq
    #
    vx
    cX
    wral
    #
    cE
    c1
    cN
    cfz
    co
    #
    wcel
    #
    @1
    @5
    wa
    @0
    cN
    vy
    cv
    #
    @2
    c.x
    co
    #
    c.0
    wceq
    #
    vx
    cX
    wral
    #
    vy
    cn
    crab
    #
    wcel
    #
    @7
    @11
    @5
    vy
    cN
    cn
    @8
    cN
    wceq
    #
    @10
    @4
    vx
    cX
    @14
    @9
    @3
    c.0
    @8
    cN
    @2
    c.x
    oveq1
    eqeq1d
    ralbidv
    elrab
    @0
    @13
    wa
    #
    cE
    @12
    cr
    clt
    cinf
    #
    @6
    @0
    @13
    cE
    @12
    c0
    wceq
    cc0
    @16
    cif
    #
    @16
    vx
    vy
    c.x
    cE
    cG
    @12
    cV
    cX
    c.0
    gexcl.1
    gexid.3
    gexid.4
    gexcl.2
    @12
    eqid
    gexval
    @13
    @12
    c0
    wne
    #
    @17
    @16
    wceq
    @12
    cN
    ne0i
    #
    @12
    c0
    cc0
    @16
    ifnefalse
    syl
    sylan9eq
    @15
    @16
    @6
    wcel
    #
    @16
    cn
    wcel
    #
    @16
    cN
    cle
    wbr
    #
    @15
    @12
    cn
    @16
    @11
    vy
    cn
    ssrab2
    #
    @15
    @12
    c1
    cuz
    cfv
    #
    wss
    #
    @18
    @16
    @12
    wcel
    @12
    cn
    @24
    @23
    nnuz
    sseqtri
    #
    @13
    @18
    @0
    @19
    adantl
    @12
    c1
    infssuzcl
    sylancr
    sseldi
    @13
    @22
    @0
    @25
    @13
    @22
    @26
    cN
    @12
    c1
    infssuzle
    mpan
    adantl
    @13
    @20
    @21
    @22
    wa
    wb
    #
    @0
    @13
    cN
    cz
    wcel
    @27
    @13
    cN
    @11
    vy
    cN
    cn
    elrabi
    nnzd
    @16
    cN
    fznn
    syl
    adantl
    mpbir2and
    eqeltrd
    sylan2br
    3impb
end
