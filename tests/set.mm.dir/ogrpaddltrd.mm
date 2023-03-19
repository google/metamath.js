include "co.mm"
include "wbr.mm"
include "coppg.mm"
include "cfv.mm"
include "cplt.mm"
include "cplusg.mm"
include "cogrp.mm"
include "wcel.mm"
include "wceq.mm"
include "eqid.mm"
include "oppglt.mm"
include "syl.mm"
include "breqd.mm"
include "mpbid.mm"
include "oppgbas.mm"
include "ogrpaddlt.mm"
include "syl131anc.mm"
include "oppgplus.mm"
include "3brtr3g.mm"
include "mpbird.mm"

theorem ogrpaddltrd
  let wph: wff ph
  let cB: class B
  let c.pl: class .+
  let c.lt: class .<
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume ogrpaddlt.0: |- B = ( Base ` G )
  assume ogrpaddlt.1: |- .< = ( lt ` G )
  assume ogrpaddlt.2: |- .+ = ( +g ` G )
  assume ogrpaddltrd.1: |- ( ph -> G e. V )
  assume ogrpaddltrd.2: |- ( ph -> ( oppG ` G ) e. oGrp )
  assume ogrpaddltrd.3: |- ( ph -> X e. B )
  assume ogrpaddltrd.4: |- ( ph -> Y e. B )
  assume ogrpaddltrd.5: |- ( ph -> Z e. B )
  assume ogrpaddltrd.6: |- ( ph -> X .< Y )


  assert |- ( ph -> ( Z .+ X ) .< ( Z .+ Y ) )

  proof
    wph
    cZ
    cX
    c.pl
    co
    #
    cZ
    cY
    c.pl
    co
    #
    c.lt
    wbr
    @0
    @1
    cG
    coppg
    cfv
    #
    cplt
    cfv
    #
    wbr
    wph
    cX
    cZ
    @2
    cplusg
    cfv
    #
    co
    #
    cY
    cZ
    @4
    co
    #
    @0
    @1
    @3
    wph
    @2
    cogrp
    wcel
    cX
    cB
    wcel
    cY
    cB
    wcel
    cZ
    cB
    wcel
    cX
    cY
    @3
    wbr
    #
    @5
    @6
    @3
    wbr
    ogrpaddltrd.2
    ogrpaddltrd.3
    ogrpaddltrd.4
    ogrpaddltrd.5
    wph
    cX
    cY
    c.lt
    wbr
    @7
    ogrpaddltrd.6
    wph
    c.lt
    @3
    cX
    cY
    wph
    cG
    cV
    wcel
    c.lt
    @3
    wceq
    ogrpaddltrd.1
    cG
    c.lt
    @2
    cV
    @2
    eqid
    #
    ogrpaddlt.1
    oppglt
    syl
    #
    breqd
    mpbid
    cB
    @4
    @3
    @2
    cX
    cY
    cZ
    cB
    cG
    @2
    @8
    ogrpaddlt.0
    oppgbas
    @3
    eqid
    @4
    eqid
    #
    ogrpaddlt
    syl131anc
    c.pl
    @4
    cG
    @2
    cX
    cZ
    ogrpaddlt.2
    @8
    @10
    oppgplus
    c.pl
    @4
    cG
    @2
    cY
    cZ
    ogrpaddlt.2
    @8
    @10
    oppgplus
    3brtr3g
    wph
    c.lt
    @3
    @0
    @1
    @9
    breqd
    mpbird
end
