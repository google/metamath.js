include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cuni.mm"
include "c0.mm"
include "clspn.mm"
include "cfv.mm"
include "wss.mm"
include "wceq.mm"
include "0ss.mm"
include "eqid.mm"
include "lsslsp.mm"
include "mp3an3.mm"
include "lsp0.mm"
include "adantr.mm"
include "lsslmod.mm"
include "syl.mm"
include "3eqtr3rd.mm"
include "unieqd.mm"
include "c0g.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "unisn.mm"
include "3eqtr3g.mm"

theorem lss0v
  let cU: class U
  let cL: class L
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let cZ: class Z
  assume lss0v.x: |- X = ( W |`s U )
  assume lss0v.o: |- .0. = ( 0g ` W )
  assume lss0v.z: |- Z = ( 0g ` X )
  assume lss0v.l: |- L = ( LSubSp ` W )


  assert |- ( ( W e. LMod /\ U e. L ) -> Z = .0. )

  proof
    cW
    clmod
    wcel
    #
    cU
    cL
    wcel
    #
    wa
    #
    cZ
    csn
    #
    cuni
    c.0
    csn
    #
    cuni
    cZ
    c.0
    @2
    @3
    @4
    @2
    c0
    cW
    clspn
    cfv
    #
    cfv
    #
    c0
    cX
    clspn
    cfv
    #
    cfv
    #
    @4
    @3
    @0
    @1
    c0
    cU
    wss
    @6
    @8
    wceq
    cU
    0ss
    cU
    c0
    cL
    @5
    @7
    cW
    cX
    lss0v.x
    @5
    eqid
    #
    @7
    eqid
    #
    lss0v.l
    lsslsp
    mp3an3
    @0
    @6
    @4
    wceq
    @1
    @5
    cW
    c.0
    lss0v.o
    @9
    lsp0
    adantr
    @2
    cX
    clmod
    wcel
    @8
    @3
    wceq
    cL
    cU
    cW
    cX
    lss0v.x
    lss0v.l
    lsslmod
    @7
    cX
    cZ
    lss0v.z
    @10
    lsp0
    syl
    3eqtr3rd
    unieqd
    cZ
    cZ
    cX
    c0g
    cfv
    cvv
    lss0v.z
    cX
    c0g
    fvex
    eqeltri
    unisn
    c.0
    c.0
    cW
    c0g
    cfv
    cvv
    lss0v.o
    cW
    c0g
    fvex
    eqeltri
    unisn
    3eqtr3g
end
