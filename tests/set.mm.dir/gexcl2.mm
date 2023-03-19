include "cgrp.mm"
include "wcel.mm"
include "cfn.mm"
include "cv.mm"
include "cod.mm"
include "cfv.mm"
include "c1.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "wral.mm"
include "cn.mm"
include "wa.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "eqid.mm"
include "odcl2.mm"
include "cdvds.mm"
include "oddvds2.mm"
include "cz.mm"
include "wi.mm"
include "nnzd.mm"
include "c0.mm"
include "wne.mm"
include "grpbn0.mm"
include "3ad2ant1.mm"
include "wb.mm"
include "hashnncl.mm"
include "3ad2ant2.mm"
include "mpbird.mm"
include "dvdsle.mm"
include "syl2anc.mm"
include "mpd.mm"
include "fznn.mm"
include "syl.mm"
include "mpbir2and.mm"
include "3expa.mm"
include "ralrimiva.mm"
include "gexcl3.mm"
include "syldan.mm"

theorem gexcl2
  let cE: class E
  let cG: class G
  let cX: class X
  let vx: setvar x
  assume gexcl2.1: |- X = ( Base ` G )
  assume gexcl2.2: |- E = ( gEx ` G )


  assert |- ( ( G e. Grp /\ X e. Fin ) -> E e. NN )

  proof
    cG
    cgrp
    wcel
    #
    cX
    cfn
    wcel
    #
    vx
    cv
    #
    cG
    cod
    cfv
    #
    cfv
    #
    c1
    cX
    chash
    cfv
    #
    cfz
    co
    wcel
    #
    vx
    cX
    wral
    cE
    cn
    wcel
    @0
    @1
    wa
    @6
    vx
    cX
    @0
    @1
    @2
    cX
    wcel
    #
    @6
    @0
    @1
    @7
    w3a
    #
    @6
    @4
    cn
    wcel
    #
    @4
    @5
    cle
    wbr
    #
    @2
    cG
    @3
    cX
    gexcl2.1
    @3
    eqid
    #
    odcl2
    #
    @8
    @4
    @5
    cdvds
    wbr
    #
    @10
    @2
    cG
    @3
    cX
    gexcl2.1
    @11
    oddvds2
    @8
    @4
    cz
    wcel
    @5
    cn
    wcel
    #
    @13
    @10
    wi
    @8
    @4
    @12
    nnzd
    @8
    @14
    cX
    c0
    wne
    #
    @0
    @1
    @15
    @7
    cX
    cG
    gexcl2.1
    grpbn0
    3ad2ant1
    @1
    @0
    @14
    @15
    wb
    @7
    cX
    hashnncl
    3ad2ant2
    mpbird
    #
    @4
    @5
    dvdsle
    syl2anc
    mpd
    @8
    @5
    cz
    wcel
    @6
    @9
    @10
    wa
    wb
    @8
    @5
    @16
    nnzd
    @4
    @5
    fznn
    syl
    mpbir2and
    3expa
    ralrimiva
    vx
    cE
    cG
    @5
    @3
    cX
    gexcl2.1
    gexcl2.2
    @11
    gexcl3
    syldan
end
