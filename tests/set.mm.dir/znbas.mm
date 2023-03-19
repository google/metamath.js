include "cn0.mm"
include "wcel.mm"
include "cz.mm"
include "cqs.mm"
include "zring.mm"
include "cqus.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "cvv.mm"
include "crg.mm"
include "eqidd.mm"
include "wceq.mm"
include "zringbas.mm"
include "a1i.mm"
include "csn.mm"
include "cqg.mm"
include "ovex.mm"
include "eqeltri.mm"
include "zringring.mm"
include "qusbas.mm"
include "oveq2i.mm"
include "znbas2.mm"
include "eqtrd.mm"

theorem znbas
  let cR: class R
  let cS: class S
  let cN: class N
  let cY: class Y
  assume znbas.s: |- S = ( RSpan ` ZZring )
  assume znbas.y: |- Y = ( Z/nZ ` N )
  assume znbas.r: |- R = ( ZZring ~QG ( S ` { N } ) )


  assert |- ( N e. NN0 -> ( ZZ /. R ) = ( Base ` Y ) )

  proof
    cN
    cn0
    wcel
    #
    cz
    cR
    cqs
    zring
    cR
    cqus
    co
    #
    cbs
    cfv
    cY
    cbs
    cfv
    @0
    cR
    zring
    @1
    cz
    cvv
    crg
    @0
    @1
    eqidd
    cz
    zring
    cbs
    cfv
    wceq
    @0
    zringbas
    a1i
    cR
    cvv
    wcel
    @0
    cR
    zring
    cN
    csn
    cS
    cfv
    #
    cqg
    co
    #
    cvv
    znbas.r
    zring
    @2
    cqg
    ovex
    eqeltri
    a1i
    zring
    crg
    wcel
    @0
    zringring
    a1i
    qusbas
    cS
    @1
    cN
    cY
    znbas.s
    cR
    @3
    zring
    cqus
    znbas.r
    oveq2i
    znbas.y
    znbas2
    eqtrd
end
