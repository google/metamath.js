include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cle.mm"
include "cordt.mm"
include "cfv.mm"
include "crest.mm"
include "ctopon.mm"
include "cxrs.mm"
include "cress.mm"
include "ctopn.mm"
include "xrge0topn.mm"
include "eqtri.mm"
include "cxr.mm"
include "wcel.mm"
include "wss.mm"
include "letopon.mm"
include "iccssxr.mm"
include "resttopon.mm"
include "mp2an.mm"
include "eqeltri.mm"
include "ccnfld.mm"
include "cvv.mm"
include "wceq.mm"
include "fvex.mm"
include "cico.mm"
include "icossicc.mm"
include "sstri.mm"
include "ovex.mm"
include "restabs.mm"
include "mp3an.mm"
include "oveq1i.mm"
include "cr.mm"
include "rge0ssre.mm"
include "eqid.mm"
include "xrrest2.mm"
include "ax-mp.mm"
include "3eqtr4i.mm"
include "cc.mm"
include "ax-resscn.mm"
include "lmlim.mm"

theorem lmlimxrge0
  let wph: wff ph
  let cP: class P
  let cF: class F
  let cJ: class J
  let cX: class X
  assume lmlimxrge0.j: |- J = ( TopOpen ` ( RR*s |`s ( 0 [,] +oo ) ) )
  assume lmlimxrge0.f: |- ( ph -> F : NN --> X )
  assume lmlimxrge0.p: |- ( ph -> P e. X )
  assume lmlimxrge0.x: |- X C_ ( 0 [,) +oo )


  assert |- ( ph -> ( F ( ~~>t ` J ) P <-> F ~~> P ) )

  proof
    wph
    cP
    cF
    cJ
    cX
    cc0
    cpnf
    cicc
    co
    #
    cJ
    cle
    cordt
    cfv
    #
    @0
    crest
    co
    #
    @0
    ctopon
    cfv
    #
    cJ
    cxrs
    @0
    cress
    co
    ctopn
    cfv
    @2
    lmlimxrge0.j
    xrge0topn
    eqtri
    #
    @1
    cxr
    ctopon
    cfv
    wcel
    @0
    cxr
    wss
    @2
    @3
    wcel
    letopon
    cc0
    cpnf
    iccssxr
    @0
    @1
    cxr
    resttopon
    mp2an
    eqeltri
    lmlimxrge0.f
    lmlimxrge0.p
    @2
    cX
    crest
    co
    #
    @1
    cX
    crest
    co
    #
    cJ
    cX
    crest
    co
    ccnfld
    ctopn
    cfv
    #
    cX
    crest
    co
    #
    @1
    cvv
    wcel
    cX
    @0
    wss
    @0
    cvv
    wcel
    @5
    @6
    wceq
    cle
    cordt
    fvex
    cX
    cc0
    cpnf
    cico
    co
    #
    @0
    lmlimxrge0.x
    cc0
    cpnf
    icossicc
    sstri
    cc0
    cpnf
    cicc
    ovex
    cX
    @0
    @1
    cvv
    cvv
    restabs
    mp3an
    cJ
    @2
    cX
    crest
    @4
    oveq1i
    cX
    cr
    wss
    @8
    @6
    wceq
    cX
    @9
    cr
    lmlimxrge0.x
    rge0ssre
    sstri
    #
    cX
    @7
    @1
    @7
    eqid
    @1
    eqid
    xrrest2
    ax-mp
    3eqtr4i
    cX
    cr
    cc
    @10
    ax-resscn
    sstri
    lmlim
end
