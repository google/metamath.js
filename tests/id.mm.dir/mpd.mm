
axiom mpd(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch) {
  assume mpd.1: $|- ( ph -> ps )$;
  assume mpd.2: $|- ( ph -> ( ps -> ch ) )$;

  return $|- ( ph -> ch )$;
}
