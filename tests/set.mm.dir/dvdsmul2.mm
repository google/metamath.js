include "cz.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "zmulcl.mm"
include "w3a.mm"
include "wceq.mm"
include "eqid.mm"
include "dvds0lem.mm"
include "mpan2.mm"
include "mpd3an3.mm"

theorem dvdsmul2
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> N || ( M x. N ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cM
    cN
    cmul
    co
    #
    cz
    wcel
    #
    cN
    @2
    cdvds
    wbr
    #
    cM
    cN
    zmulcl
    @0
    @1
    @3
    w3a
    @2
    @2
    wceq
    @4
    @2
    eqid
    cM
    cN
    @2
    dvds0lem
    mpan2
    mpd3an3
end
