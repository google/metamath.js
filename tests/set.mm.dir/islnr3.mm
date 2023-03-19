include "clnr.mm"
include "wcel.mm"
include "crg.mm"
include "cv.mm"
include "crsp.mm"
include "cfv.mm"
include "wceq.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "cnacs.mm"
include "eqid.mm"
include "islnr2.mm"
include "cacs.mm"
include "cmrc.mm"
include "mrcrsp.mm"
include "fveq1d.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "lidlacs.mm"
include "biantrurd.mm"
include "bitrd.mm"
include "isnacs.mm"
include "syl6bbr.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem islnr3
  let cB: class B
  let cR: class R
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  assume islnr3.b: |- B = ( Base ` R )
  assume islnr3.u: |- U = ( LIdeal ` R )


  assert |- ( R e. LNoeR <-> ( R e. Ring /\ U e. ( NoeACS ` B ) ) )

  proof
    cR
    clnr
    wcel
    cR
    crg
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    crsp
    cfv
    #
    cfv
    #
    wceq
    #
    vy
    cB
    cpw
    cfn
    cin
    #
    wrex
    #
    vx
    cU
    wral
    #
    wa
    @0
    cU
    cB
    cnacs
    cfv
    wcel
    #
    wa
    cB
    cR
    cU
    vy
    vx
    @3
    islnr3.b
    islnr3.u
    @3
    eqid
    #
    islnr2
    @0
    @8
    @9
    @0
    @8
    cU
    cB
    cacs
    cfv
    wcel
    #
    @1
    @2
    cU
    cmrc
    cfv
    #
    cfv
    #
    wceq
    #
    vy
    @6
    wrex
    #
    vx
    cU
    wral
    #
    wa
    #
    @9
    @0
    @8
    @16
    @17
    @0
    @7
    @15
    vx
    cU
    @0
    @5
    @14
    vy
    @6
    @0
    @4
    @13
    @1
    @0
    @2
    @3
    @12
    cR
    cU
    @12
    @3
    islnr3.u
    @10
    @12
    eqid
    #
    mrcrsp
    fveq1d
    eqeq2d
    rexbidv
    ralbidv
    @0
    @11
    @16
    cB
    cU
    cR
    islnr3.b
    islnr3.u
    lidlacs
    biantrurd
    bitrd
    cU
    vy
    @12
    cB
    vx
    @18
    isnacs
    syl6bbr
    pm5.32i
    bitri
end
