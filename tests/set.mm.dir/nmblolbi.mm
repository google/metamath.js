include "wcel.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "c0o.mm"
include "cif.mm"
include "wceq.mm"
include "fveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "breq12d.mm"
include "imbi2d.mm"
include "cnv.mm"
include "eqid.mm"
include "0blo.mm"
include "mp2an.mm"
include "elimel.mm"
include "nmblolbii.mm"
include "dedth.mm"
include "imp.mm"

theorem nmblolbi
  let cA: class A
  let cB: class B
  let cT: class T
  let cU: class U
  let cL: class L
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  assume nmblolbi.1: |- X = ( BaseSet ` U )
  assume nmblolbi.4: |- L = ( normCV ` U )
  assume nmblolbi.5: |- M = ( normCV ` W )
  assume nmblolbi.6: |- N = ( U normOpOLD W )
  assume nmblolbi.7: |- B = ( U BLnOp W )
  assume nmblolbi.u: |- U e. NrmCVec
  assume nmblolbi.w: |- W e. NrmCVec


  assert |- ( ( T e. B /\ A e. X ) -> ( M ` ( T ` A ) ) <_ ( ( N ` T ) x. ( L ` A ) ) )

  proof
    cT
    cB
    wcel
    #
    cA
    cX
    wcel
    #
    cA
    cT
    cfv
    #
    cM
    cfv
    #
    cT
    cN
    cfv
    #
    cA
    cL
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    @0
    @1
    @7
    wi
    @1
    cA
    @0
    cT
    cU
    cW
    c0o
    co
    #
    cif
    #
    cfv
    #
    cM
    cfv
    #
    @9
    cN
    cfv
    #
    @5
    cmul
    co
    #
    cle
    wbr
    #
    wi
    cT
    @8
    cT
    @9
    wceq
    #
    @7
    @14
    @1
    @15
    @3
    @11
    @6
    @13
    cle
    @15
    @2
    @10
    cM
    cA
    cT
    @9
    fveq1
    fveq2d
    @15
    @4
    @12
    @5
    cmul
    cT
    @9
    cN
    fveq2
    oveq1d
    breq12d
    imbi2d
    cA
    cB
    @9
    cU
    cL
    cM
    cN
    cW
    cX
    nmblolbi.1
    nmblolbi.4
    nmblolbi.5
    nmblolbi.6
    nmblolbi.7
    nmblolbi.u
    nmblolbi.w
    cT
    @8
    cB
    cU
    cnv
    wcel
    cW
    cnv
    wcel
    @8
    cB
    wcel
    nmblolbi.u
    nmblolbi.w
    cB
    cU
    cW
    @8
    @8
    eqid
    nmblolbi.7
    0blo
    mp2an
    elimel
    nmblolbii
    dedth
    imp
end
