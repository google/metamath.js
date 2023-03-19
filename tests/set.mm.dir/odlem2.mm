include "wcel.mm"
include "cn.mm"
include "co.mm"
include "wceq.mm"
include "cfv.mm"
include "c1.mm"
include "cfz.mm"
include "wa.mm"
include "cv.mm"
include "crab.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "c0.mm"
include "cc0.mm"
include "cif.mm"
include "eqid.mm"
include "odval.mm"
include "n0i.mm"
include "iffalsed.mm"
include "sylan9eq.mm"
include "cle.mm"
include "wbr.mm"
include "ssrab2.mm"
include "cuz.mm"
include "wss.mm"
include "wne.mm"
include "nnuz.mm"
include "sseqtri.mm"
include "ne0i.mm"
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
include "syl.mm"
include "mpbir2and.mm"
include "eqeltrd.mm"
include "sylan2br.mm"
include "3impb.mm"

theorem odlem2
  let cA: class A
  let c.x: class .x.
  let cG: class G
  let cN: class N
  let cO: class O
  let cX: class X
  let c.0: class .0.
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vx: setvar x
  assume odcl.1: |- X = ( Base ` G )
  assume odcl.2: |- O = ( od ` G )
  assume odid.3: |- .x. = ( .g ` G )
  assume odid.4: |- .0. = ( 0g ` G )


  assert |- ( ( A e. X /\ N e. NN /\ ( N .x. A ) = .0. ) -> ( O ` A ) e. ( 1 ... N ) )

  proof
    cA
    cX
    wcel
    #
    cN
    cn
    wcel
    #
    cN
    cA
    c.x
    co
    #
    c.0
    wceq
    #
    cA
    cO
    cfv
    #
    c1
    cN
    cfz
    co
    #
    wcel
    #
    @1
    @3
    wa
    @0
    cN
    vy
    cv
    #
    cA
    c.x
    co
    #
    c.0
    wceq
    #
    vy
    cn
    crab
    #
    wcel
    #
    @6
    @9
    @3
    vy
    cN
    cn
    @7
    cN
    wceq
    @8
    @2
    c.0
    @7
    cN
    cA
    c.x
    oveq1
    eqeq1d
    elrab
    @0
    @11
    wa
    #
    @4
    @10
    cr
    clt
    cinf
    #
    @5
    @0
    @11
    @4
    @10
    c0
    wceq
    #
    cc0
    @13
    cif
    @13
    vy
    cA
    c.x
    cG
    @10
    cO
    cX
    c.0
    odcl.1
    odid.3
    odid.4
    odcl.2
    @10
    eqid
    odval
    @11
    @14
    cc0
    @13
    @10
    cN
    n0i
    iffalsed
    sylan9eq
    @12
    @13
    @5
    wcel
    #
    @13
    cn
    wcel
    #
    @13
    cN
    cle
    wbr
    #
    @12
    @10
    cn
    @13
    @9
    vy
    cn
    ssrab2
    #
    @12
    @10
    c1
    cuz
    cfv
    #
    wss
    #
    @10
    c0
    wne
    #
    @13
    @10
    wcel
    @10
    cn
    @19
    @18
    nnuz
    sseqtri
    #
    @11
    @21
    @0
    @10
    cN
    ne0i
    adantl
    @10
    c1
    infssuzcl
    sylancr
    sseldi
    @11
    @17
    @0
    @20
    @11
    @17
    @22
    cN
    @10
    c1
    infssuzle
    mpan
    adantl
    @11
    @15
    @16
    @17
    wa
    wb
    #
    @0
    @11
    cN
    cz
    wcel
    @23
    @11
    cN
    @9
    vy
    cN
    cn
    elrabi
    nnzd
    @13
    cN
    fznn
    syl
    adantl
    mpbir2and
    eqeltrd
    sylan2br
    3impb
end
