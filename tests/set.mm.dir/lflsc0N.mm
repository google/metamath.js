include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "co.mm"
include "cvv.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "crg.mm"
include "clmod.mm"
include "lmodring.mm"
include "syl.mm"
include "ring0cl.mm"
include "ofc12.mm"
include "wceq.mm"
include "ringlz.mm"
include "syl2anc.mm"
include "sneqd.mm"
include "xpeq2d.mm"
include "eqtrd.mm"

theorem lflsc0N
  let wph: wff ph
  let cD: class D
  let c.x: class .x.
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume lflsc0.v: |- V = ( Base ` W )
  assume lflsc0.d: |- D = ( Scalar ` W )
  assume lflsc0.k: |- K = ( Base ` D )
  assume lflsc0.t: |- .x. = ( .r ` D )
  assume lflsc0.o: |- .0. = ( 0g ` D )
  assume lflsc0.w: |- ( ph -> W e. LMod )
  assume lflsc0.x: |- ( ph -> X e. K )


  assert |- ( ph -> ( ( V X. { .0. } ) oF .x. ( V X. { X } ) ) = ( V X. { .0. } ) )

  proof
    wph
    cV
    c.0
    csn
    #
    cxp
    #
    cV
    cX
    csn
    cxp
    c.x
    cof
    co
    cV
    c.0
    cX
    c.x
    co
    #
    csn
    #
    cxp
    @1
    wph
    cV
    c.0
    cX
    c.x
    cvv
    cK
    cK
    cV
    cvv
    wcel
    wph
    cV
    cW
    cbs
    cfv
    cvv
    lflsc0.v
    cW
    cbs
    fvex
    eqeltri
    a1i
    wph
    cD
    crg
    wcel
    #
    c.0
    cK
    wcel
    wph
    cW
    clmod
    wcel
    @4
    lflsc0.w
    cD
    cW
    lflsc0.d
    lmodring
    syl
    #
    cK
    cD
    c.0
    lflsc0.k
    lflsc0.o
    ring0cl
    syl
    lflsc0.x
    ofc12
    wph
    @3
    @0
    cV
    wph
    @2
    c.0
    wph
    @4
    cX
    cK
    wcel
    @2
    c.0
    wceq
    @5
    lflsc0.x
    cK
    cD
    c.x
    cX
    c.0
    lflsc0.k
    lflsc0.t
    lflsc0.o
    ringlz
    syl2anc
    sneqd
    xpeq2d
    eqtrd
end
