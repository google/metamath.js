include "cnrg.mm"
include "wcel.mm"
include "cabv.mm"
include "cfv.mm"
include "c0g.mm"
include "wne.mm"
include "c1.mm"
include "wceq.mm"
include "cnzr.mm"
include "eqid.mm"
include "nrgabv.mm"
include "nzrnz.mm"
include "abv1z.mm"
include "syl2an.mm"

theorem nm1
  let cR: class R
  let c.1: class .1.
  let cN: class N
  assume nm1.n: |- N = ( norm ` R )
  assume nm1.u: |- .1. = ( 1r ` R )


  assert |- ( ( R e. NrmRing /\ R e. NzRing ) -> ( N ` .1. ) = 1 )

  proof
    cR
    cnrg
    wcel
    cN
    cR
    cabv
    cfv
    #
    wcel
    c.1
    cR
    c0g
    cfv
    #
    wne
    c.1
    cN
    cfv
    c1
    wceq
    cR
    cnzr
    wcel
    @0
    cR
    cN
    nm1.n
    @0
    eqid
    #
    nrgabv
    cR
    c.1
    @1
    nm1.u
    @1
    eqid
    #
    nzrnz
    @0
    cR
    c.1
    cN
    @1
    @2
    nm1.u
    @3
    abv1z
    syl2an
end
