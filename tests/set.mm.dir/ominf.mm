include "com.mm"
include "cfn.mm"
include "wcel.mm"
include "wn.mm"
include "wi.mm"
include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "wrex.mm"
include "isfi.mm"
include "wpss.mm"
include "wss.mm"
include "wne.mm"
include "wa.mm"
include "word.mm"
include "wb.mm"
include "nnord.mm"
include "ordom.mm"
include "ordelssne.mm"
include "sylancl.mm"
include "ibi.mm"
include "df-pss.mm"
include "sylibr.mm"
include "ensym.mm"
include "pssinf.mm"
include "syl2an.mm"
include "rexlimiva.mm"
include "sylbi.mm"
include "pm2.01.mm"
include "ax-mp.mm"

theorem ominf
  let vx: setvar x


  assert |- -. _om e. Fin

  proof
    com
    cfn
    wcel
    #
    @0
    wn
    #
    wi
    @1
    @0
    com
    vx
    cv
    #
    cen
    wbr
    #
    vx
    com
    wrex
    @1
    vx
    com
    isfi
    @3
    @1
    vx
    com
    @2
    com
    wcel
    #
    @2
    com
    wpss
    #
    @2
    com
    cen
    wbr
    @1
    @3
    @4
    @2
    com
    wss
    @2
    com
    wne
    wa
    #
    @5
    @4
    @6
    @4
    @2
    word
    com
    word
    @4
    @6
    wb
    @2
    nnord
    ordom
    @2
    com
    ordelssne
    sylancl
    ibi
    @2
    com
    df-pss
    sylibr
    com
    @2
    ensym
    @2
    com
    pssinf
    syl2an
    rexlimiva
    sylbi
    @0
    pm2.01
    ax-mp
end
